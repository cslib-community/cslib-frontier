/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Commitment.Scheme
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Basic
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Credit
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Dedup

/-!
# Extracted credit conservation for single-issuer VOLE-ACT

This module proves an extracted-model reduction step for credit conservation in single-issuer
VOLE-ACT. The game, both parts of the argument and the reductions are original to this library.
The source draft leaves the protocol's security reductions open ([VOLEACT2026], Security
Considerations / Proof status).

The protocol data follow the draft. A token certifies `Tag(Com(nf, ctx, t, r), x)` ([VOLEACT2026],
Overview and Protocol Specification / Parameters / Tag). Issuance certifies `Tag(c, 0)` for a
commitment `c` to `(nf, ctx, T)` (Protocol Specification / Initial Issuance). A spend reveals `nf`,
debits `d` and commits to the change state as `c'`; the issuer then certifies `Tag(c', x')` for a
refund `x'` it grants. The spend relation checks that the input state was certified (V1), that `c'`
opens to the change state (V2), and that `t + x = t' + d` over the integers (V3). The caller
rejects a nullifier it has already recorded (Protocol Specification / Spending and Spend Response).

Here the commitment is any function `com : Nullifier → Context → ℕ → Opening → Commitment`, the
tag is any `tag : Commitment → ℕ → Target`, and the certifier is any
`S : Signature.Scheme PK SK Target Sig`. Targets use the two-stage encoder `Credit.target com tag`,
and semantic notes reuse `Credit.Note`. The KP800 and MQ instantiations are the intended uses and
are not formalized here. The game is a permissive modeling choice. It omits the range checks (V4,
and `T ≥ 1` at issuance), and every amount `T`, debit `d` and refund `x'` comes from the
adversary's request. In the draft, `T` is agreed out of band and is the issuer's own input, and the
issuer chooses `x'`. The bounds below hold for this game as stated. `IssuerBridge`
(`CslibFrontier/Crypto/Protocols/AnonymousToken/IssuerBridge.lean`) transfers them without
probability loss to a stateful, probabilistic draft-style issuer with issuer-agreed initial
balances, issuer-chosen refunds, and range rejections.

In the extracted model, every request carries the witness that a knowledge extractor for its
VOLEitH proof would output, next to its public statement, and the issuer checks the relation on
that witness directly. The knowledge-extraction error of the VOLEitH proof system, zero-knowledge,
random-oracle or ideal-permutation arguments for `Tag` and `Com`, Keccak, the UOV instantiation,
multi-issuer selection and runtime bounds are all outside this module. The results are therefore
a reduction step toward credit conservation, not a credit-conservation theorem for the
unextracted protocol.

Part I (`spentDebit_le_of_certified`) is the deterministic accounting core. Take any list of
requests, in any order, in which every spend satisfies the balance equation `t + x = t' + d` (V3),
spent `(ctx, nf)` pairs are pairwise distinct, and every spend's input note is the output note of
some request in the list. Then `∑ d ≤ ∑ T + ∑ x'` in every context. Part I involves no
commitment function, tag function or signature scheme, and no commitment-binding premise.

Part II is the adaptive game. `extractedConservationExperiment` runs the adversary against an
issuer oracle built on `ProbOracleComp.runLogWith`. The issuer signs `tag c 0` or `tag c' x'` from
public data only and rejects a reused `(ctx, nf)` against its log. The adversary wins if, in a
context it names at the end, debits exceed issued credit plus refunds. The explicit reduction
`noteForger` simulates the issuer with a semantic signing oracle. When the adversary wins, Part I
yields a spend whose input note was never certified, so `noteForger` wins
`Cslib.Crypto.AnonymousToken.extractedExperiment`
(`extractedConservationExperiment_succProbability_le_extractedExperiment`). Composing with
`extracted_succProbability_le` bounds the game by the EUF-CMA success of `targetForger` plus the
probability that the forger's run contains a target collision (`bindingExperiment`), each with
coefficient one (`extractedConservationExperiment_succProbability_le`). As in `Basic`, the EUF-CMA
term is for chosen targets, so it need not be small for a raw UOV map. For `tag = Prod.mk`, the
target-collision term is in turn bounded by the binding game of a keyless
`Cslib.Crypto.Commitment.Scheme`, one whose verifier, under every key, accepts exactly when
`com nf ctx t o = c` (`bindingExperiment_prod_mk_le_commitment`). Keyed commitments, whose
verifier depends on the key, are out of scope.

The totals here do not reuse `Credit.Ledger`. The ledger is a sequential state invariant, while
Part I is a statement about an unordered transcript and does not depend on execution order.

## Main definitions

* `IssueRequest`, `SpendRequest`, `Request`: extracted-witness issuance and spend requests, with
  `SpendRequest.inputNote`, `SpendRequest.inputPayload`, `Request.outputPayload`, and the public
  `Request.signedMessage`.
* `acceptLocal`, `hasSpentNullifier`, `acceptRequest`, `validTrace`: per-request checks (V1, V2,
  V3) and stateful nullifier uniqueness across an oldest-first accepted trace.
* `issuedAmount`, `spentDebit`, `grantedRefund`: context-scoped credit totals.
* `findNoteForgery`: explicit post-run search for a spend whose input `Credit.Note` is not among
  the accepted output notes.
* `extractedIssuerOracle`, `ExtractedAdversary`, `ExtractedConservationExecution`,
  `runExtractedConservation`, `extractedConservationAccept`, `extractedConservationExperiment`:
  the extracted credit-conservation game.
* `noteForgerHandler`, `noteForger`: explicit simulation reduction to `ExtractedForger`.
* `commitmentBindingReduction`: for `tag = Prod.mk`, explicit reduction from target collisions to
  a double opening of `com`.

## Main results

* `acceptLocal_of_validTrace`, `balance_of_validTrace`, `nodup_spends_of_validTrace`: invariants of
  accepted traces.
* `spentDebit_le_of_certified`: deterministic, order-independent accounting core
  (`∑ d ≤ ∑ T + ∑ x'`).
* `noteForger_queryBound`: `noteForger` queries the signing oracle at most once per request of the
  adversary; with `targetForger_queryBound` the same holds for `targetForger` on `noteForger`.
* `runExtractedConservation_log_length_le`: a `q`-query adversary logs at most `q` accepted
  requests.
* `extractedConservationExperiment_succProbability_le_extractedExperiment`: the game is bounded by
  `extractedExperiment S (Credit.target com tag) (noteForger com tag S A)`.
* `extractedConservationExperiment_succProbability_le`: the game is bounded by the EUF-CMA success
  of `targetForger` plus the target-collision probability on `noteForger`.
* `checkBindingWitness_prod_mk_iff`: for `tag = Prod.mk`, a target binding witness is equivalent
  to equal refunds, distinct `(nullifier, ctx, credit)` triples, and equal commitments.
* `bindingExperiment_prod_mk_le_commitment`,
  `extractedConservationExperiment_succProbability_le_prod_mk`: for `tag = Prod.mk`, the
  target-collision term is bounded by the binding of a keyless commitment scheme.

## References

* [*VOLE-ACT*][VOLEACT2026], Overview (`#overview`), Protocol Specification / Parameters / Tag
  (`#tag`), Initial Issuance (`#issuance`) and Spending (`#spending`), and Security
  Considerations / Proof status (`#proof-status`).
-/

public section

namespace Cslib.Crypto.AnonymousToken.Conservation

open Probability

variable {Nullifier Context Opening Commitment Target PK SK Sig : Type}

/- The requests, checks, totals, game and `noteForger` are exposed so that clients can evaluate
them with `decide` and `simp`. The commitment-binding reduction at the end is not. -/
@[expose] section

/-! ### Requests, payloads, and acceptance checks -/

/-- An extracted issuance request (`issue ctx T c` with witness `(nf, r)`). -/
structure IssueRequest (Nullifier Context Opening Commitment : Type) where
  /-- Issuance context `ctx`. -/
  ctx : Context
  /-- Initial credited amount `T`. -/
  amount : ℕ
  /-- Commitment `c` to `(nullifier, ctx, amount)` under `opening`. -/
  commitment : Commitment
  /-- Extracted nullifier `nf`. -/
  nullifier : Nullifier
  /-- Extracted opening randomness `r`. -/
  opening : Opening
  deriving DecidableEq

/-- An extracted spend request (`spend ctx nf d x' c'` with witness `(t, r, x, s, nf', t', r')`). -/
structure SpendRequest (Nullifier Context Opening Commitment Sig : Type) where
  /-- Issuance context `ctx` shared by input and change tokens. -/
  ctx : Context
  /-- Revealed nullifier `nf` of the spent token. -/
  nullifier : Nullifier
  /-- Amount `d` debited by this spend. -/
  debit : ℕ
  /-- Refund `x'` granted by the issuer on the change token. -/
  refund : ℕ
  /-- Commitment `c'` to the change token. -/
  changeCommitment : Commitment
  /-- Extracted committed balance `t` of the input token. -/
  oldCredit : ℕ
  /-- Extracted opening randomness `r` of the input token. -/
  oldOpening : Opening
  /-- Extracted prior refund `x` carried by the input token. -/
  oldRefund : ℕ
  /-- Extracted certification signature `s` on `Credit.target com tag inputNote oldOpening`. -/
  signature : Sig
  /-- Extracted nullifier `nf'` of the change token. -/
  newNullifier : Nullifier
  /-- Extracted committed balance `t'` of the change token. -/
  newCredit : ℕ
  /-- Extracted opening randomness `r'` of the change token. -/
  newOpening : Opening
  deriving DecidableEq

/-- An adversary request to the extracted single-issuer VOLE-ACT oracle. -/
inductive Request (Nullifier Context Opening Commitment Sig : Type) where
  /-- Issuance request `issue ctx T c` with extracted witness `(nf, r)`. -/
  | issue (req : IssueRequest Nullifier Context Opening Commitment)
  /-- Spend request `spend ctx nf d x' c'` with extracted witness `(t, r, x, s, nf', t', r')`. -/
  | spend (req : SpendRequest Nullifier Context Opening Commitment Sig)
  deriving DecidableEq

/-- The issuance context targeted by a request. -/
def Request.ctx : Request Nullifier Context Opening Commitment Sig → Context
  | .issue req => req.ctx
  | .spend req => req.ctx

/-- The target message signed by the real issuer when `req` is accepted: `tag c 0` for
issuance, `tag c' x'` for spend. Notice this depends only on the public commitment and refund. -/
def Request.signedMessage (tag : Commitment → ℕ → Target) :
    Request Nullifier Context Opening Commitment Sig → Target
  | .issue req => tag req.commitment 0
  | .spend req => tag req.changeCommitment req.refund

/-- The semantic input `Credit.Note` consumed by a spend request. -/
def SpendRequest.inputNote
    (req : SpendRequest Nullifier Context Opening Commitment Sig) :
    Credit.Note Nullifier Context :=
  ⟨req.nullifier, req.ctx, req.oldCredit, req.oldRefund⟩

/-- The semantic input payload `(inputNote, oldOpening)` certified by `req.signature`. -/
def SpendRequest.inputPayload
    (req : SpendRequest Nullifier Context Opening Commitment Sig) :
    Payload (Credit.Note Nullifier Context) Opening :=
  ⟨req.inputNote, req.oldOpening⟩

/-- The semantic output payload created by an accepted request: `(⟨nf, ctx, T, 0⟩, r)` for
issuance and `(⟨nf', ctx, t', x'⟩, r')` for spend. -/
def Request.outputPayload :
    Request Nullifier Context Opening Commitment Sig →
    Payload (Credit.Note Nullifier Context) Opening
  | .issue req => ⟨⟨req.nullifier, req.ctx, req.amount, 0⟩, req.opening⟩
  | .spend req => ⟨⟨req.newNullifier, req.ctx, req.newCredit, req.refund⟩, req.newOpening⟩

/-- Per-request validity checks, independent of prior spent nullifiers:
for issuance, `com nf ctx T r = c`; for spend, `(V1)` verification on
`Credit.target com tag inputNote oldOpening`, `(V2)` change commitment opening
`com nf' ctx t' r' = c'`, and `(V3)` natural-number balance conservation `t + x = t' + d` (no
modular wraparound). The draft's `(V4)` range bounds are omitted here and enforced in
`Cslib.Crypto.AnonymousToken.IssuerBridge` (`acceptDraftIssue`, `acceptDraftSpendPre`). -/
def acceptLocal [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK) :
    Request Nullifier Context Opening Commitment Sig → Bool
  | .issue req => decide (com req.nullifier req.ctx req.amount req.opening = req.commitment)
  | .spend req =>
      S.verify pk (Credit.target com tag req.inputNote req.oldOpening) req.signature &&
      decide (com req.newNullifier req.ctx req.newCredit req.newOpening = req.changeCommitment) &&
      decide (req.oldCredit + req.oldRefund = req.newCredit + req.debit)

/-- Whether `(ctx, nf)` already appears as the spent nullifier of an accepted spend in `reqs`.
The draft keeps nullifier records per issuer key and issuance context ([VOLEACT2026], Protocol
Specification / Spend Response); with the single issuer key here, that scope is `(ctx, nf)`. -/
def hasSpentNullifier [DecidableEq Nullifier] [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) (nf : Nullifier) : Bool :=
  reqs.any fun
    | .issue _ => false
    | .spend s => decide (s.ctx = ctx ∧ s.nullifier = nf)

/-- Full issuer acceptance check for `req` given `pk` and accepted prefix `accepted`. -/
def acceptRequest [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK)
    (accepted : List (Request Nullifier Context Opening Commitment Sig)) :
    Request Nullifier Context Opening Commitment Sig → Bool
  | .issue req => acceptLocal com tag S pk (.issue req)
  | .spend req =>
      acceptLocal com tag S pk (.spend req) && !hasSpentNullifier accepted req.ctx req.nullifier

/-- Check that an oldest-first request trace `reqs` is sequentially accepted starting from the
already-accepted prefix `accepted`. -/
def validTraceFrom [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK) :
    List (Request Nullifier Context Opening Commitment Sig) →
    List (Request Nullifier Context Opening Commitment Sig) → Bool
  | _, [] => true
  | accepted, req :: rest =>
      acceptRequest com tag S pk accepted req &&
        validTraceFrom com tag S pk (accepted ++ [req]) rest

/-- Check that an oldest-first request trace `reqs` is sequentially accepted from empty history. -/
abbrev validTrace [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK)
    (reqs : List (Request Nullifier Context Opening Commitment Sig)) : Bool :=
  validTraceFrom com tag S pk [] reqs

/-! ### Accounting quantities and forgery search -/

/-- All spend requests in `reqs`, preserving order. -/
def spends (reqs : List (Request Nullifier Context Opening Commitment Sig)) :
    List (SpendRequest Nullifier Context Opening Commitment Sig) :=
  reqs.filterMap fun
    | .issue _ => none
    | .spend req => some req

/-- All issuance requests in `reqs` targeting context `ctx`. -/
def issuesIn [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) :
    List (IssueRequest Nullifier Context Opening Commitment) :=
  reqs.filterMap fun
    | .issue req => if req.ctx = ctx then some req else none
    | .spend _ => none

/-- All spend requests in `reqs` targeting context `ctx`. -/
def spendsIn [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) :
    List (SpendRequest Nullifier Context Opening Commitment Sig) :=
  (spends reqs).filter fun s => decide (s.ctx = ctx)

/-- Total issued credit `∑ T` across accepted issuances in context `ctx`. -/
def issuedAmount [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) : ℕ :=
  ((issuesIn reqs ctx).map IssueRequest.amount).sum

/-- Total debited credit `∑ d` across accepted spends in context `ctx`. -/
def spentDebit [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) : ℕ :=
  ((spendsIn reqs ctx).map SpendRequest.debit).sum

/-- Total granted refunds `∑ x'` across accepted spends in context `ctx`. -/
def grantedRefund [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) : ℕ :=
  ((spendsIn reqs ctx).map SpendRequest.refund).sum

/-- Search `reqs` for the first spend whose input `Credit.Note` never appears as an output note of
any request in `reqs`, returning the semantic forgery witness `⟨s.inputPayload, s.signature⟩`. -/
def findNoteForgery [DecidableEq Nullifier] [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig)) :
    Option (Token (Credit.Note Nullifier Context) Opening Sig) :=
  let certified := reqs.map fun r => r.outputPayload.message
  (spends reqs).findSome? fun s =>
    if s.inputNote ∈ certified then none else some ⟨s.inputPayload, s.signature⟩

/-! ### Part I: Deterministic accounting core -/

private theorem spends_cons_issue (ir : IssueRequest Nullifier Context Opening Commitment)
    (rest : List (Request Nullifier Context Opening Commitment Sig)) :
    spends (.issue ir :: rest) = spends rest := rfl

private theorem spends_cons_spend (sr : SpendRequest Nullifier Context Opening Commitment Sig)
    (rest : List (Request Nullifier Context Opening Commitment Sig)) :
    spends (.spend sr :: rest) = sr :: spends rest := rfl

private theorem issuesIn_cons_issue [DecidableEq Context]
    (ir : IssueRequest Nullifier Context Opening Commitment)
    (rest : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) :
    issuesIn (.issue ir :: rest) ctx =
      if ir.ctx = ctx then ir :: issuesIn rest ctx else issuesIn rest ctx := by
  simp only [issuesIn, List.filterMap_cons]
  split_ifs <;> rfl

private theorem issuesIn_cons_spend [DecidableEq Context]
    (sr : SpendRequest Nullifier Context Opening Commitment Sig)
    (rest : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) :
    issuesIn (.spend sr :: rest) ctx = issuesIn rest ctx := rfl

private theorem spendsIn_cons_issue [DecidableEq Context]
    (ir : IssueRequest Nullifier Context Opening Commitment)
    (rest : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) :
    spendsIn (.issue ir :: rest) ctx = spendsIn rest ctx := rfl

private theorem spendsIn_cons_spend [DecidableEq Context]
    (sr : SpendRequest Nullifier Context Opening Commitment Sig)
    (rest : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) :
    spendsIn (.spend sr :: rest) ctx =
      if sr.ctx = ctx then sr :: spendsIn rest ctx else spendsIn rest ctx := by
  simp only [spendsIn, spends_cons_spend, List.filter_cons, decide_eq_true_eq]

private theorem validTraceFrom_append
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK)
    (acc xs : List (Request Nullifier Context Opening Commitment Sig))
    (y : Request Nullifier Context Opening Commitment Sig) :
    validTraceFrom com tag S pk acc (xs ++ [y]) =
      (validTraceFrom com tag S pk acc xs && acceptRequest com tag S pk (acc ++ xs) y) := by
  induction xs generalizing acc with
  | nil => simp [validTraceFrom]
  | cons x xs ih =>
    simp only [List.cons_append, validTraceFrom, ih (acc ++ [x]), List.append_assoc,
      List.nil_append, Bool.and_assoc]

private theorem hasSpentNullifier_append_left
    [DecidableEq Nullifier] [DecidableEq Context]
    (xs ys : List (Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) (nf : Nullifier)
    (h : hasSpentNullifier xs ctx nf = true) :
    hasSpentNullifier (xs ++ ys) ctx nf = true := by
  simp only [hasSpentNullifier, List.any_eq_true] at h ⊢
  obtain ⟨r, hr, hmatch⟩ := h
  exact ⟨r, List.mem_append_left ys hr, hmatch⟩

private theorem acceptLocal_of_acceptRequest
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {pk : PK}
    {accepted : List (Request Nullifier Context Opening Commitment Sig)}
    {req : Request Nullifier Context Opening Commitment Sig}
    (h : acceptRequest com tag S pk accepted req = true) :
    acceptLocal com tag S pk req = true := by
  cases req with
  | issue _ => exact h
  | spend _ => exact (Bool.and_eq_true_iff.mp h).1

private theorem acceptLocal_of_validTraceFrom
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {pk : PK}
    {acc reqs : List (Request Nullifier Context Opening Commitment Sig)}
    (h : validTraceFrom com tag S pk acc reqs = true) :
    ∀ r ∈ reqs, acceptLocal com tag S pk r = true := by
  induction reqs generalizing acc with
  | nil => simp
  | cons req rest ih =>
    simp only [validTraceFrom, Bool.and_eq_true] at h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact acceptLocal_of_acceptRequest h.1
    · exact ih h.2 r hr

private theorem not_hasSpentNullifier_of_validTraceFrom
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {pk : PK}
    {acc reqs : List (Request Nullifier Context Opening Commitment Sig)}
    (h : validTraceFrom com tag S pk acc reqs = true) :
    ∀ s ∈ spends reqs, hasSpentNullifier acc s.ctx s.nullifier = false := by
  induction reqs generalizing acc with
  | nil => simp [spends]
  | cons req rest ih =>
    simp only [validTraceFrom, Bool.and_eq_true] at h
    intro s hs
    have hprev (hs' : s ∈ spends rest) : hasSpentNullifier acc s.ctx s.nullifier = false :=
      Bool.eq_false_iff.mpr fun htrue =>
        Bool.false_ne_true ((ih h.2 s hs').symm.trans
          (hasSpentNullifier_append_left acc [req] s.ctx s.nullifier htrue))
    cases req with
    | issue ir => exact hprev hs
    | spend sr =>
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Bool.eq_false_iff.mpr (by
          simpa [acceptRequest, Bool.and_eq_true] using (Bool.and_eq_true_iff.mp h.1).2)
      · exact hprev hs

private theorem nodup_spends_of_validTraceFrom
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {pk : PK}
    {acc reqs : List (Request Nullifier Context Opening Commitment Sig)}
    (h : validTraceFrom com tag S pk acc reqs = true) :
    ((spends reqs).map fun s => (s.ctx, s.nullifier)).Nodup := by
  induction reqs generalizing acc with
  | nil => simp [spends]
  | cons req rest ih =>
    simp only [validTraceFrom, Bool.and_eq_true] at h
    cases req with
    | issue ir =>
      rw [spends_cons_issue]
      exact ih h.2
    | spend sr =>
      rw [spends_cons_spend, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro hmem
      obtain ⟨s, hs, heq⟩ := List.mem_map.mp hmem
      have htrue : hasSpentNullifier (acc ++ [.spend sr]) s.ctx s.nullifier = true :=
        List.any_eq_true.mpr ⟨.spend sr, by simp,
          decide_eq_true ⟨(Prod.mk.inj heq).1.symm, (Prod.mk.inj heq).2.symm⟩⟩
      simp [not_hasSpentNullifier_of_validTraceFrom h.2 s hs] at htrue

/-- Every request in a `validTrace` satisfies its local check (`acceptLocal`). -/
theorem acceptLocal_of_validTrace
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {pk : PK}
    {reqs : List (Request Nullifier Context Opening Commitment Sig)}
    (h : validTrace com tag S pk reqs = true) :
    ∀ r ∈ reqs, Conservation.acceptLocal com tag S pk r = true :=
  acceptLocal_of_validTraceFrom h

/-- Spend `(ctx, nullifier)` pairs are pairwise distinct across a `validTrace`. -/
theorem nodup_spends_of_validTrace
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {pk : PK}
    {reqs : List (Request Nullifier Context Opening Commitment Sig)}
    (h : validTrace com tag S pk reqs = true) :
    ((spends reqs).map fun s => (s.ctx, s.nullifier)).Nodup :=
  nodup_spends_of_validTraceFrom h

private theorem mem_reqs_of_mem_spends
    {reqs : List (Request Nullifier Context Opening Commitment Sig)}
    {s : SpendRequest Nullifier Context Opening Commitment Sig}
    (hs : s ∈ spends reqs) : Request.spend s ∈ reqs := by
  simp only [spends, List.mem_filterMap] at hs
  obtain ⟨r, hr, hsome⟩ := hs
  cases r with
  | issue _ => simp at hsome
  | spend sr =>
    cases hsome
    exact hr

/-- The `(V3)` balance equation of every spend in a list whose requests pass `acceptLocal`. -/
private theorem balance_of_acceptLocal [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {pk : PK}
    {reqs : List (Request Nullifier Context Opening Commitment Sig)}
    (hlocal : ∀ r ∈ reqs, acceptLocal com tag S pk r = true) :
    ∀ s ∈ spends reqs, s.oldCredit + s.oldRefund = s.newCredit + s.debit := by
  intro s hs
  have hr := hlocal (.spend s) (mem_reqs_of_mem_spends hs)
  simp only [acceptLocal, Bool.and_eq_true, decide_eq_true_eq] at hr
  exact hr.2

/-- Every spend in a trace accepted by `validTrace` satisfies the `(V3)` balance equation, the
first premise of `spentDebit_le_of_certified`. -/
theorem balance_of_validTrace
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {pk : PK}
    {reqs : List (Request Nullifier Context Opening Commitment Sig)}
    (h : validTrace com tag S pk reqs = true) :
    ∀ s ∈ spends reqs, s.oldCredit + s.oldRefund = s.newCredit + s.debit :=
  balance_of_acceptLocal (acceptLocal_of_validTrace h)

private theorem sum_balance_outputPayload_filter [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig)) (ctx : Context) :
    ((reqs.filter fun r => decide (r.ctx = ctx)).map
        fun r => r.outputPayload.message.balance).sum =
      issuedAmount reqs ctx +
        (((spendsIn reqs ctx).map SpendRequest.newCredit).sum + grantedRefund reqs ctx) := by
  induction reqs with
  | nil => simp [issuedAmount, issuesIn, spendsIn, spends, grantedRefund]
  | cons r rest ih =>
    cases r with
    | issue ir =>
      by_cases hctx : ir.ctx = ctx
      · simp only [List.filter_cons, Request.ctx, hctx, decide_true, ↓reduceIte, List.map_cons,
          Request.outputPayload, Credit.Note.balance, List.sum_cons, issuedAmount,
          issuesIn_cons_issue, spendsIn_cons_issue, grantedRefund] at ih ⊢
        omega
      · simp only [List.filter_cons, Request.ctx, hctx, decide_false, Bool.false_eq_true,
          ↓reduceIte, issuedAmount, issuesIn_cons_issue, spendsIn_cons_issue, grantedRefund]
          at ih ⊢
        exact ih
    | spend sr =>
      by_cases hctx : sr.ctx = ctx
      · simp only [List.filter_cons, Request.ctx, hctx, decide_true, ↓reduceIte, List.map_cons,
          Request.outputPayload, Credit.Note.balance, List.sum_cons, issuedAmount,
          issuesIn_cons_spend, spendsIn_cons_spend, grantedRefund] at ih ⊢
        omega
      · simp only [List.filter_cons, Request.ctx, hctx, decide_false, Bool.false_eq_true,
          ↓reduceIte, issuedAmount, issuesIn_cons_spend, spendsIn_cons_spend, grantedRefund]
          at ih ⊢
        exact ih

private theorem sum_balance_inputNote_list
    (l : List (SpendRequest Nullifier Context Opening Commitment Sig))
    (hmem : ∀ s ∈ l, s.oldCredit + s.oldRefund = s.newCredit + s.debit) :
    (l.map fun s => s.inputNote.balance).sum =
      (l.map SpendRequest.newCredit).sum + (l.map SpendRequest.debit).sum := by
  induction l with
  | nil => simp
  | cons s rest ih =>
    have hs := hmem s List.mem_cons_self
    have ih' := ih fun s' hs' => hmem s' (List.mem_cons_of_mem s hs')
    simp only [List.map_cons, SpendRequest.inputNote, Credit.Note.balance, List.sum_cons] at ih' ⊢
    omega

private theorem sum_map_le_sum_map_of_nodup {α : Type*}
    (A B : List α) (w : α → ℕ) (hnd : A.Nodup) (hsub : ∀ x ∈ A, x ∈ B) :
    (A.map w).sum ≤ (B.map w).sum := by
  classical
  have hfin : A.toFinset ⊆ B.toFinset := fun x hx =>
    List.mem_toFinset.mpr (hsub x (List.mem_toFinset.mp hx))
  calc (A.map w).sum
      = ∑ x ∈ A.toFinset, w x := (List.sum_toFinset w hnd).symm
    _ ≤ ∑ x ∈ B.toFinset, w x := Finset.sum_le_sum_of_subset hfin
    _ = ∑ x ∈ B.dedup.toFinset, w x := by rw [List.toFinset_dedup]
    _ = (B.dedup.map w).sum := List.sum_toFinset w (List.nodup_dedup B)
    _ ≤ (B.map w).sum := ((List.dedup_sublist B).map w).sum_le_sum (fun _ _ => Nat.zero_le _)

private theorem outputPayload_context
    (r : Request Nullifier Context Opening Commitment Sig) :
    r.outputPayload.message.context = r.ctx := by
  cases r <;> rfl

/-- Extracted-model accounting step, original to this library: for any request list `reqs`
(in any order) in which every spend satisfies the balance equation `t + x = t' + d` (the `(V3)`
check of `acceptLocal`), spent `(ctx, nullifier)` pairs are pairwise distinct, and every spend's
semantic input `Credit.Note` matches some request's output `Credit.Note`, total debited credit in
every context `ctx` is at most total issued credit plus total granted refunds in `ctx`. This step is
deterministic. No commitment, tag, signature, or opening check enters it, so it needs no
commitment-binding or signature premise. -/
theorem spentDebit_le_of_certified [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig))
    (hbalance : ∀ s ∈ spends reqs, s.oldCredit + s.oldRefund = s.newCredit + s.debit)
    (hnodup : ((spends reqs).map fun s => (s.ctx, s.nullifier)).Nodup)
    (hcertified : ∀ s ∈ spends reqs,
      s.inputNote ∈ reqs.map (fun r => r.outputPayload.message))
    (ctx : Context) :
    spentDebit reqs ctx ≤ issuedAmount reqs ctx + grantedRefund reqs ctx := by
  let spCtx := spendsIn reqs ctx
  let reqsCtx := reqs.filter fun r => decide (r.ctx = ctx)
  let inList := spCtx.map SpendRequest.inputNote
  let outList := reqsCtx.map fun r => r.outputPayload.message
  have hnodup_key : (spCtx.map fun s => (s.ctx, s.nullifier)).Nodup :=
    hnodup.sublist (List.filter_sublist.map _)
  have hnodup_in : inList.Nodup := by
    have hcomp :
        (inList.map fun n => (n.context, n.nullifier)) =
          spCtx.map fun s => (s.ctx, s.nullifier) := by
      simp [inList, List.map_map, Function.comp_def, SpendRequest.inputNote]
    exact List.Nodup.of_map (fun n => (n.context, n.nullifier)) (hcomp ▸ hnodup_key)
  have hsub_in_out : ∀ n ∈ inList, n ∈ outList := by
    intro n hn
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hn
    obtain ⟨hsp, hsctx⟩ := List.mem_filter.mp hs
    obtain ⟨r, hr, hreq⟩ := List.mem_map.mp (hcertified s hsp)
    have hrctx : r.ctx = ctx := by
      have hctx_note := congrArg Credit.Note.context hreq
      rw [outputPayload_context] at hctx_note
      exact hctx_note.trans (of_decide_eq_true hsctx)
    refine List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, decide_eq_true hrctx⟩, hreq⟩
  have hsum_le := sum_map_le_sum_map_of_nodup inList outList Credit.Note.balance hnodup_in
    hsub_in_out
  have hin :
      (inList.map Credit.Note.balance).sum =
        (spCtx.map SpendRequest.newCredit).sum + spentDebit reqs ctx := by
    simpa only [inList, spCtx, spentDebit, List.map_map, Function.comp_def] using
      sum_balance_inputNote_list (spendsIn reqs ctx) fun s hs =>
        hbalance s (List.mem_filter.mp hs).1
  have hout :
      (outList.map Credit.Note.balance).sum =
        issuedAmount reqs ctx + ((spCtx.map SpendRequest.newCredit).sum + grantedRefund reqs ctx) :=
    by
    simpa only [outList, List.map_map, Function.comp_def] using
      sum_balance_outputPayload_filter reqs ctx
  omega

/-- `findNoteForgery reqs = none` iff every spend in `reqs` uses a certified input note. -/
theorem findNoteForgery_eq_none_iff [DecidableEq Nullifier] [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig)) :
    findNoteForgery reqs = none ↔
      ∀ s ∈ spends reqs, s.inputNote ∈ reqs.map (fun r => r.outputPayload.message) := by
  simp only [findNoteForgery, List.findSome?_eq_none_iff, ite_eq_left_iff, reduceCtorEq, imp_false,
    Decidable.not_not]

/-- If `findNoteForgery reqs = some tok`, then `tok` is the payload/signature pair of some spend
in `reqs` whose input note never appeared among the output notes in `reqs`. -/
theorem findNoteForgery_eq_some [DecidableEq Nullifier] [DecidableEq Context]
    {reqs : List (Request Nullifier Context Opening Commitment Sig)}
    {tok : Token (Credit.Note Nullifier Context) Opening Sig}
    (h : findNoteForgery reqs = some tok) :
    ∃ s ∈ spends reqs,
      tok = ⟨s.inputPayload, s.signature⟩ ∧
        s.inputNote ∉ reqs.map (fun r => r.outputPayload.message) := by
  simp only [findNoteForgery, List.findSome?_eq_some_iff] at h
  obtain ⟨_, s, _, hsp, hfound, _⟩ := h
  by_cases hmem : s.inputNote ∈ reqs.map (fun r => r.outputPayload.message)
  · simp [hmem] at hfound
  · simp only [hmem, ↓reduceIte, Option.some.injEq] at hfound
    exact ⟨s, by simp [hsp], hfound.symm, hmem⟩

/-! ### Part II: Adaptive game, reduction to `AnonymousToken`, and probability bound -/

/-- The log-reading issuer oracle passed to `ProbOracleComp.runLogWith`: if `req` is accepted
given `pk` and the previously logged accepted requests, return
`some (some <$> S.sign sk (req.signedMessage tag))`; otherwise return `none`, in which case
`runLogWith` answers `default` (here `none : Option Sig`) and does not log the request. -/
def extractedIssuerOracle
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (log : List (Request Nullifier Context Opening Commitment Sig × Option Sig))
    (req : Request Nullifier Context Opening Commitment Sig) :
    Option (ProbComp (Option Sig)) :=
  if acceptRequest com tag S keys.1 (log.map Prod.fst) req then
    some (some <$> S.sign keys.2 (req.signedMessage tag))
  else
    none

/-- An adaptive adversary in the extracted VOLE-ACT credit-conservation game: given `pk`, it
queries the extracted issuer oracle and outputs the context `ctx*` it claims is violated. -/
abbrev ExtractedAdversary (Nullifier Context Opening Commitment PK Sig : Type) :=
  PK → ProbOracleComp
    (fun _ : Request Nullifier Context Opening Commitment Sig => Option Sig) Context

/-- The public key, target context, and accepted transcript of a credit-conservation run. -/
structure ExtractedConservationExecution (Nullifier Context Opening Commitment PK Sig : Type) where
  /-- Public verification key sampled by the experiment. -/
  publicKey : PK
  /-- Target context `ctx*` output by the adversary. -/
  targetCtx : Context
  /-- Accepted requests paired with their issued `some σ` replies, oldest first. -/
  log : List (Request Nullifier Context Opening Commitment Sig × Option Sig)

/-- Execute `A` against the extracted VOLE-ACT issuer. -/
def runExtractedConservation
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    ProbComp (ExtractedConservationExecution Nullifier Context Opening Commitment PK Sig) := do
  let keys ← S.keyGen
  let (targetCtx, log) ← (A keys.1).runLogWith (extractedIssuerOracle com tag S keys)
  return ⟨keys.1, targetCtx, log⟩

/-- Acceptance predicate of the credit-conservation game: under `run.targetCtx`, total spend
debits strictly exceed total issued credit plus total granted refunds. -/
def extractedConservationAccept [DecidableEq Context]
    (run : ExtractedConservationExecution Nullifier Context Opening Commitment PK Sig) : Bool :=
  let reqs := run.log.map Prod.fst
  decide (issuedAmount reqs run.targetCtx + grantedRefund reqs run.targetCtx <
    spentDebit reqs run.targetCtx)

/-- The extracted VOLE-ACT credit-conservation experiment, original to this library (the source
draft states no security game): the adversary submits requests whose witnesses are given in the
clear, and wins if the accepted transcript overspends `run.targetCtx`. The error of extracting
those witnesses from VOLEitH proofs is outside this model. -/
def extractedConservationExperiment
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) : Experiment :=
  extractedConservationAccept <$> runExtractedConservation com tag S A

/-- Stateful simulation handler used by `noteForger`: forwards each accepted request's
`req.outputPayload` to the external semantic signing oracle once while recording accepted requests;
rejected requests make no oracle query and return `none`. -/
def noteForgerHandler
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK)
    (req : Request Nullifier Context Opening Commitment Sig) :
    StateT (List (Request Nullifier Context Opening Commitment Sig))
      (ProbOracleComp (fun _ : Payload (Credit.Note Nullifier Context) Opening => Sig))
      (Option Sig) :=
  fun accepted =>
    if acceptRequest com tag S pk accepted req then do
      let σ ← ProbOracleComp.query req.outputPayload
      return (some σ, accepted ++ [req])
    else
      pure (none, accepted)

/-- Explicit semantic-forgery reduction `noteForger` from `ExtractedAdversary` to
`ExtractedForger PK (Credit.Note Nullifier Context) Opening Sig`: simulates the VOLE-ACT issuer
via `noteForgerHandler` and outputs the first spend whose input `Credit.Note` never appeared among
accepted output notes. The `Inhabited` instances only supply a default token for the branch where
no such spend exists; there the conservation game is lost by `spentDebit_le_of_certified`, so the
default does not affect the bound. -/
def noteForger
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    ExtractedForger PK (Credit.Note Nullifier Context) Opening Sig := fun pk => do
  let (_, accepted) ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (noteForgerHandler com tag S pk))
    (A pk)).run []
  return (findNoteForgery accepted).getD ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩

/-- `noteForger` makes at most `q` semantic-signing queries whenever `A` makes at most `q`
issuer requests. No runtime bound or fair-coin efficiency follows from this oracle-call bound
alone. -/
theorem noteForger_queryBound
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) (pk : PK) {q : ℕ}
    (hA : (A pk).IsQueryBounded q) :
    (noteForger com tag S A pk).IsQueryBounded q := by
  have hbody :
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (noteForgerHandler com tag S pk))
        (A pk)).run []).IsQueryBounded q := by
    refine OracleComp.IsCostBounded.run_interpret (fun r accepted => ?_) hA []
    rcases r with k | req
    · simpa [OracleComp.sumHandler, StateT.run, StateT.lift] using
        (ProbOracleComp.IsQueryBounded.sample
          (spec := fun _ : Payload (Credit.Note Nullifier Context) Opening => Sig)
          (ProbComp.unifFin k)).bind fun a => OracleComp.IsCostBounded.pure (a, accepted) 0
    · simp only [OracleComp.sumHandler, Sum.elim_inr, StateT.run, noteForgerHandler]
      split_ifs
      · exact (ProbOracleComp.IsQueryBounded.query
          (spec := fun _ : Payload (Credit.Note Nullifier Context) Opening => Sig)
          req.outputPayload).bind fun σ =>
            OracleComp.IsCostBounded.pure (some σ, accepted ++ [req]) 0
      · exact OracleComp.IsCostBounded.pure (none, accepted) 1
  exact hbody.bind fun _ => OracleComp.IsCostBounded.pure _ 0

/-- A `q`-query adversary logs at most `q` accepted requests in `runExtractedConservation`. -/
theorem runExtractedConservation_log_length_le
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) {q : ℕ}
    (hA : ∀ pk, (A pk).IsQueryBounded q)
    {run : ExtractedConservationExecution Nullifier Context Opening Commitment PK Sig}
    (hrun : run ∈ (ProbComp.eval (runExtractedConservation com tag S A)).support) :
    run.log.length ≤ q := by
  simp only [runExtractedConservation, ProbComp.eval_bind, PMF.mem_support_bind_iff,
    ProbComp.eval_pure, PMF.mem_support_pure_iff] at hrun
  obtain ⟨keys, -, result, hresult, rfl⟩ := hrun
  exact (hA keys.1).length_runLogWith_le _ _ hresult

private theorem target_outputPayload_eq_signedMessage
    [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {pk : PK}
    {req : Request Nullifier Context Opening Commitment Sig}
    (h : acceptLocal com tag S pk req = true) :
    Credit.target com tag req.outputPayload.message req.outputPayload.opening =
      req.signedMessage tag := by
  cases req with
  | issue ir =>
    simp only [acceptLocal, decide_eq_true_eq] at h
    simp only [Credit.target, Request.outputPayload, Request.signedMessage, h]
  | spend sr =>
    simp only [acceptLocal, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Credit.target, Request.outputPayload, Request.signedMessage, h.1.2]

private theorem runLogWith_extractedIssuerOracle_invariant
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig)
    {result : Context × List (Request Nullifier Context Opening Commitment Sig × Option Sig)}
    (hres :
      result ∈
        (ProbComp.eval ((A keys.1).runLogWith (extractedIssuerOracle com tag S keys))).support) :
    validTrace com tag S keys.1 (result.2.map Prod.fst) = true ∧
      ∀ p ∈ result.2, p.2.isSome = true := by
  rw [ProbOracleComp.runLogWith, ProbOracleComp.eval_runState] at hres
  refine ProbOracleComp.runWith_invariant
    (fun req log =>
      ProbComp.eval (ProbOracleComp.logOracle (extractedIssuerOracle com tag S keys) req log))
    (fun log => validTrace com tag S keys.1 (log.map Prod.fst) = true ∧
      ∀ p ∈ log, p.2.isSome = true)
    (fun req log ⟨hvalid, hsome⟩ a log' hstep => ?_)
    (A keys.1) [] ⟨rfl, by simp⟩ result.1 result.2 hres
  dsimp only [ProbOracleComp.logOracle, extractedIssuerOracle] at hstep
  split_ifs at hstep with hacc
  · simp only [Functor.map_map, ProbComp.eval_map, PMF.mem_support_map_iff, Prod.mk.injEq] at hstep
    obtain ⟨σ, -, rfl, rfl⟩ := hstep
    refine ⟨?_, ?_⟩
    · rw [List.map_append, List.map_cons, List.map_nil]
      change validTraceFrom com tag S keys.1 [] (log.map Prod.fst ++ [req]) = true
      rw [validTraceFrom_append]
      exact Bool.and_eq_true_iff.mpr ⟨hvalid, hacc⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hsome p hp
      · obtain rfl := List.mem_singleton.mp hp
        rfl
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
    obtain ⟨-, rfl⟩ := hstep
    exact ⟨hvalid, hsome⟩

private def toExtractedExecution
    [DecidableEq Nullifier] [DecidableEq Context]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (run : ExtractedConservationExecution Nullifier Context Opening Commitment PK Sig) :
    Execution PK (Credit.Note Nullifier Context) Opening Sig :=
  ⟨run.publicKey,
    (findNoteForgery (run.log.map Prod.fst)).getD ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩,
    run.log.filterMap fun p => p.2.map fun σ => (p.1.outputPayload, σ)⟩

private theorem runExtracted_noteForger_eq
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    ProbComp.eval (runExtracted S (Credit.target com tag) (noteForger com tag S A)) =
      ProbComp.eval (toExtractedExecution <$> runExtractedConservation com tag S A) := by
  simp only [runExtracted, runExtractedConservation, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure]
  rw [PMF.map_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ _ => ?_
  dsimp only
  let represent : List (Request Nullifier Context Opening Commitment Sig × Option Sig) →
      List (Request Nullifier Context Opening Commitment Sig) ×
        List (Payload (Credit.Note Nullifier Context) Opening × Sig) :=
    fun log =>
      (log.map Prod.fst,
        log.filterMap fun p => p.2.map fun σ => (p.1.outputPayload, σ))
  let targetSigner :
      List (Payload (Credit.Note Nullifier Context) Opening × Sig) →
      Payload (Credit.Note Nullifier Context) Opening →
      Option (ProbComp Sig) :=
    fun _ payload => some (S.sign sk (Credit.target com tag payload.message payload.opening))
  have hrun :
      ProbComp.eval
          ((noteForger com tag S A pk).runLog
            (fun payload => S.sign sk (Credit.target com tag payload.message payload.opening))) =
        (ProbComp.eval ((A pk).runLogWith (extractedIssuerOracle com tag S (pk, sk)))).map
          fun (_, log) =>
            let acc := (represent log).1
            let out :=
              (findNoteForgery acc).getD ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩
            (out, (represent log).2) := by
    rw [← ProbOracleComp.runLogWith_some, ProbOracleComp.runLogWith, ProbOracleComp.eval_runState]
    dsimp only [noteForger]
    rw [ProbOracleComp.runWith_bind]
    rw [ProbOracleComp.runWith_run_interpret
      (noteForgerHandler com tag S pk)
      (fun payload sigLog => ProbComp.eval (ProbOracleComp.logOracle targetSigner payload sigLog))
      (A pk) [] []]
    rw [PMF.bind_map]
    have hsim :
        (ProbOracleComp.runWith
          (fun req log =>
            ProbComp.eval
              (ProbOracleComp.logOracle (extractedIssuerOracle com tag S (pk, sk)) req log))
          (A pk) []).map (fun (ctx, log) => (ctx, represent log)) =
        ProbOracleComp.runWith
          (fun req state =>
            (ProbOracleComp.runWith
              (fun payload sigLog =>
                ProbComp.eval (ProbOracleComp.logOracle targetSigner payload sigLog))
              ((noteForgerHandler com tag S pk req).run state.1) state.2).map
                fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
          (A pk) ([], []) := by
      refine ProbOracleComp.runWith_map_state _ _ represent (fun req log => ?_) (A pk) []
      dsimp only [ProbOracleComp.logOracle, extractedIssuerOracle, noteForgerHandler, StateT.run,
        targetSigner]
      split_ifs with hacc
      · simp only [Functor.map_map, ProbComp.eval_map, ProbOracleComp.runWith_bind,
          ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
          target_outputPayload_eq_signedMessage (acceptLocal_of_acceptRequest hacc),
          PMF.map_comp, PMF.bind_map, PMF.map_bind]
        congr 1 with σ : 1
        simp [represent, Function.comp_def]
      · simp only [represent, ProbComp.eval_pure, ProbOracleComp.runWith_pure, PMF.pure_map]
        rfl
    rw [ProbOracleComp.runLogWith, ProbOracleComp.eval_runState]
    rw [← hsim, PMF.bind_map]
    simp only [PMF.map, ProbOracleComp.runWith_pure, Function.comp_def]
  rw [hrun, PMF.bind_map, PMF.map_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨ctx, log⟩ _ => ?_
  simp [toExtractedExecution, represent]

private theorem extractedConservationAccept_imp_extractedAccept
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (run : ExtractedConservationExecution Nullifier Context Opening Commitment PK Sig)
    (hvalid : validTrace com tag S run.publicKey (run.log.map Prod.fst) = true)
    (hsome : ∀ p ∈ run.log, p.2.isSome = true)
    (hwin : extractedConservationAccept run = true) :
    extractedAccept S (Credit.target com tag) (toExtractedExecution run) = true := by
  let reqs := run.log.map Prod.fst
  have hlog_map :
      ((run.log.filterMap fun p => p.2.map fun σ => (p.1.outputPayload, σ)).map
          fun entry => entry.1.message) =
        reqs.map (fun r => r.outputPayload.message) := by
    dsimp only [reqs]
    generalize run.log = rawLog at hsome ⊢
    induction rawLog with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨r, _ | σ⟩
      · exact absurd (hsome (r, none) List.mem_cons_self) (by simp)
      · simpa using ih fun p hp => hsome p (List.mem_cons_of_mem _ hp)
  cases hforg : findNoteForgery reqs with
  | none =>
    exfalso
    have hcert := (findNoteForgery_eq_none_iff reqs).mp hforg
    have hle := spentDebit_le_of_certified reqs (balance_of_validTrace hvalid)
      (nodup_spends_of_validTrace hvalid) hcert run.targetCtx
    simp only [extractedConservationAccept, decide_eq_true_eq] at hwin
    exact (Nat.not_le.mpr hwin) hle
  | some tok =>
    obtain ⟨s, hs, rfl, hnotmem⟩ := findNoteForgery_eq_some hforg
    have hloc := acceptLocal_of_validTrace hvalid (.spend s) (mem_reqs_of_mem_spends hs)
    simp only [acceptLocal, Bool.and_eq_true] at hloc
    simp only [extractedAccept, toExtractedExecution, reqs, hforg, Option.getD_some,
      Token.valid, SpendRequest.inputPayload, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hloc.1.1, by rwa [hlog_map]⟩

/-- Extracted-model reduction step, original to this library; it couples the
credit-conservation game to `Cslib.Crypto.AnonymousToken.extractedExperiment`. Any adversary
winning the extracted VOLE-ACT credit-conservation game yields a winning semantic forgery via
`noteForger` with at least the same probability. -/
theorem extractedConservationExperiment_succProbability_le_extractedExperiment
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    Experiment.succProbability (extractedConservationExperiment com tag S A) ≤
      Experiment.succProbability
        (extractedExperiment S (Credit.target com tag) (noteForger com tag S A)) := by
  simp only [Experiment.succProbability, extractedConservationExperiment, extractedExperiment,
    ProbComp.eval_map, runExtracted_noteForger_eq, PMF.map_comp, Function.comp_def,
    Game.succProbability]
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  refine PMF.map_true_mono _ fun run hrun hwin => ?_
  simp only [runExtractedConservation, ProbComp.eval_bind, PMF.mem_support_bind_iff,
    ProbComp.eval_pure, PMF.mem_support_pure_iff] at hrun
  obtain ⟨keys, -, ⟨ctx, log⟩, hres, rfl⟩ := hrun
  have hinv := runLogWith_extractedIssuerOracle_invariant com tag S keys A hres
  exact extractedConservationAccept_imp_extractedAccept com tag S ⟨keys.1, ctx, log⟩ hinv.1 hinv.2
    hwin

/-- Extracted-model reduction step, original to this library; this is not a credit-conservation
theorem for the unextracted protocol. Every winning adversary against the extracted
credit-conservation game yields either a target existential forgery via
`targetForger (Credit.target com tag) (noteForger com tag S A)` or a target collision in the
forger's run, measured by `bindingExperiment S (Credit.target com tag) (noteForger com tag S A)`;
both terms have coefficient one. For `tag = Prod.mk` the second term is bounded by commitment
binding in `bindingExperiment_prod_mk_le_commitment`. The error of extracting witnesses from
VOLEitH proofs is outside this model. -/
theorem extractedConservationExperiment_succProbability_le
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment] [DecidableEq Target]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    Experiment.succProbability (extractedConservationExperiment com tag S A) ≤
      Experiment.succProbability
          (S.eufCmaExperiment (targetForger (Credit.target com tag) (noteForger com tag S A))) +
        Experiment.succProbability
          (bindingExperiment S (Credit.target com tag) (noteForger com tag S A)) :=
  (extractedConservationExperiment_succProbability_le_extractedExperiment com tag S A).trans
    (extracted_succProbability_le S (Credit.target com tag) (noteForger com tag S A))

/-- With `Target = Commitment × ℕ` and `tag := Prod.mk`, the identity encoding of `(c, x)` that
abstracts the draft's `Tag` step, a valid target binding witness for `Credit.target com Prod.mk`
is equivalent to equal refunds, distinct `(nullifier, ctx, credit)` triples, and equal `com`
evaluations. -/
theorem checkBindingWitness_prod_mk_iff
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (w : BindingWitness (Credit.Note Nullifier Context) Opening) :
    checkBindingWitness (Credit.target com Prod.mk) w = true ↔
      w.first.message.refund = w.second.message.refund ∧
        (w.first.message.nullifier, w.first.message.context, w.first.message.credit) ≠
          (w.second.message.nullifier, w.second.message.context, w.second.message.credit) ∧
        com w.first.message.nullifier w.first.message.context w.first.message.credit
            w.first.opening =
          com w.second.message.nullifier w.second.message.context w.second.message.credit
            w.second.opening := by
  rcases w with ⟨⟨⟨nf₁, ctx₁, t₁, x₁⟩, r₁⟩, ⟨⟨nf₂, ctx₂, t₂, x₂⟩, r₂⟩⟩
  simp only [checkBindingWitness, Credit.target, decide_eq_true_eq, ne_eq, Prod.mk.injEq,
    Credit.Note.mk.injEq]
  exact ⟨fun ⟨hne, hcom, rfl⟩ => ⟨rfl, fun ⟨rfl, rfl, rfl⟩ => hne ⟨rfl, rfl, rfl, rfl⟩, hcom⟩,
    fun ⟨href, htri, hcom⟩ => ⟨fun ⟨rfl, rfl, rfl, _⟩ => htri ⟨rfl, rfl, rfl⟩, hcom, href⟩⟩

end

/-- Convert a binding witness for `Credit.target com Prod.mk` into a commitment binding
collision over `(nullifier, context, credit)` triples. -/
@[expose] def noteBindingCollision
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (w : BindingWitness (Credit.Note Nullifier Context) Opening) :
    Crypto.Commitment.BindingCollision (Nullifier × Context × ℕ) Commitment Opening :=
  let n₀ := w.first.message
  let r₀ := w.first.opening
  let n₁ := w.second.message
  let r₁ := w.second.opening
  { commitment := com n₀.nullifier n₀.context n₀.credit r₀
    msg₀ := (n₀.nullifier, n₀.context, n₀.credit)
    opening₀ := r₀
    msg₁ := (n₁.nullifier, n₁.context, n₁.credit)
    opening₁ := r₁ }

/-- A valid target binding witness for `Credit.target com Prod.mk` yields a valid commitment
binding collision under any key of a keyless `Cslib.Crypto.Commitment.Scheme`, one whose verifier
accepts exactly when `com nf ctx t o = c` under every key (`hverify`). -/
private theorem isBindingCollision_noteBindingCollision
    {K : Type} [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (hverify : ∀ k nf ctx t c o, CS.verify k (nf, ctx, t) c o = decide (com nf ctx t o = c))
    {k : K} {w : BindingWitness (Credit.Note Nullifier Context) Opening}
    (h : checkBindingWitness (Credit.target com Prod.mk) w = true) :
    CS.isBindingCollision k (noteBindingCollision com w) = true := by
  have ⟨_, hne, hcom⟩ := (checkBindingWitness_prod_mk_iff com w).mp h
  simp [Crypto.Commitment.Scheme.isBindingCollision, noteBindingCollision, hverify, hne, hcom]

/-- `noteBindingCollision` on a found witness. With no witness it returns a trivial pair that
opens `com default default 0 default` twice to the same message, which is never a collision. -/
@[expose] def noteBindingCollisionOrTrivial
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening]
    (com : Nullifier → Context → ℕ → Opening → Commitment) :
    Option (BindingWitness (Credit.Note Nullifier Context) Opening) →
      Crypto.Commitment.BindingCollision (Nullifier × Context × ℕ) Commitment Opening
  | some w => noteBindingCollision com w
  | none =>
    { commitment := com default default 0 default
      msg₀ := (default, default, 0)
      opening₀ := default
      msg₁ := (default, default, 0)
      opening₁ := default }

/-- Extracted-model reduction step, original to this library: runs `bindingReduction` for
`Credit.target com Prod.mk` on `noteForger`, ignoring the commitment key. A witness with payloads
`(⟨nf₀, ctx₀, t₀, _⟩, r₀)` and `(⟨nf₁, ctx₁, t₁, _⟩, r₁)` becomes the pair of openings of
`com nf₀ ctx₀ t₀ r₀` to `(nf₀, ctx₀, t₀)` under `r₀` and to `(nf₁, ctx₁, t₁)` under `r₁`. With no
witness, the output opens `com default default 0 default` twice to the same message, which is
never a collision. -/
def commitmentBindingReduction
    {K : Type} [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (S : Signature.Scheme PK SK (Commitment × ℕ) Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    K →
      ProbComp
        (Crypto.Commitment.BindingCollision (Nullifier × Context × ℕ) Commitment Opening) :=
  fun _ =>
    noteBindingCollisionOrTrivial com <$>
      bindingReduction S (Credit.target com Prod.mk) (noteForger com Prod.mk S A)

/-- Unfolding specification for `commitmentBindingReduction` at any key `k`. -/
theorem commitmentBindingReduction_eq
    {K : Type} [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (S : Signature.Scheme PK SK (Commitment × ℕ) Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) (k : K) :
    commitmentBindingReduction com S A k =
      noteBindingCollisionOrTrivial com <$>
        bindingReduction S (Credit.target com Prod.mk) (noteForger com Prod.mk S A) := by
  rfl

/-- Extracted-model reduction step, original to this library: the target-binding success
probability of `noteForger` under `Credit.target com Prod.mk` is at most the commitment-binding
success probability of `commitmentBindingReduction` against a keyless scheme `CS`, one whose
verifier accepts exactly when `com nf ctx t o = c` under every key (`hverify`). The reduction
ignores the commitment key, so keyed commitments are out of scope. -/
theorem bindingExperiment_prod_mk_le_commitment
    {K : Type} [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (hverify : ∀ k nf ctx t c o, CS.verify k (nf, ctx, t) c o = decide (com nf ctx t o = c))
    (S : Signature.Scheme PK SK (Commitment × ℕ) Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    Experiment.succProbability
        (bindingExperiment S (Credit.target com Prod.mk) (noteForger com Prod.mk S A)) ≤
      Experiment.succProbability (CS.bindingExperiment (commitmentBindingReduction com S A)) := by
  let μ := ProbComp.eval
    (bindingReduction S (Credit.target com Prod.mk) (noteForger com Prod.mk S A))
  simp only [Experiment.succProbability, bindingExperiment,
    Crypto.Commitment.Scheme.bindingExperiment, commitmentBindingReduction, ProbComp.eval_map,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_map, Game.succProbability]
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  refine Probability.PMF.le_bind_apply_on_support (ProbComp.eval CS.keyGen) fun k _ => ?_
  change (μ.map fun witness => witness.any (checkBindingWitness (Credit.target com Prod.mk)))
      true ≤
    (μ.map fun witness => CS.isBindingCollision k (noteBindingCollisionOrTrivial com witness)) true
  refine PMF.map_true_mono μ fun witness _ hwin => ?_
  cases witness with
  | none => simp at hwin
  | some w =>
    simp only [Option.any_some] at hwin
    exact isBindingCollision_noteBindingCollision com CS hverify hwin

/-- Extracted-model reduction step, original to this library: at `tag = Prod.mk`, any adversary
winning the extracted credit-conservation game yields either a target forgery via `targetForger`
or a commitment binding collision via `commitmentBindingReduction`, for a keyless scheme `CS` whose
verifier accepts exactly when `com nf ctx t o = c` under every key (`hverify`). -/
theorem extractedConservationExperiment_succProbability_le_prod_mk
    {K : Type} [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (hverify : ∀ k nf ctx t c o, CS.verify k (nf, ctx, t) c o = decide (com nf ctx t o = c))
    (S : Signature.Scheme PK SK (Commitment × ℕ) Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    Experiment.succProbability (extractedConservationExperiment com Prod.mk S A) ≤
      Experiment.succProbability
          (S.eufCmaExperiment
            (targetForger (Credit.target com Prod.mk) (noteForger com Prod.mk S A))) +
        Experiment.succProbability (CS.bindingExperiment (commitmentBindingReduction com S A)) :=
  (extractedConservationExperiment_succProbability_le com Prod.mk S A).trans
    (add_le_add le_rfl (bindingExperiment_prod_mk_le_commitment com CS hverify S A))

end Cslib.Crypto.AnonymousToken.Conservation
