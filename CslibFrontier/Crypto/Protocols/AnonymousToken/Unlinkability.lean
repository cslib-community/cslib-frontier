/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Commitment.Scheme
public import CslibFrontier.Crypto.Computational.Signature.Scheme
public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Crypto.Game.Hybrid

/-!
# Malicious-issuer unlinkability for VOLE-ACT

This module formalizes malicious-issuer unlinkability for VOLE-ACT (`[VOLEACT2026]`, Protocol
Specification / Initial Issuance `#issuance` and Spending `#spending`) in the finite query-bounded
model (`#7068`), including:
1. **Protocol model (`OpeningCommitment`, `validStatement`, `multiProofZKRealGame` / `SimGame`)**:
   explicit statement/witness relations enforcing `(V1)` (`S.verify pk (tag c x) s`), `(V2)`
   (`c' = Com(nf', ctx, t', r')`), `(V3)` (`t' = t + x - d`), and `(V4)` range checks (`t, x, t',
   d < bound`, with `0 < T < bound` at issuance and `oldRefund = 0` on newly issued tokens,
   aligning with the `(V1)`–`(V4)` checks of `AnonymousToken.Conservation` and
   `AnonymousToken.IssuerBridge` while keeping this client-side statement-witness relation
   separate from extracted issuer accounting).
2. **Adaptive malicious-issuer unlinkability (`unlinkabilityExperiment`) and balance-partitioning
   attacks**: an adversary chooses arbitrary `(pk, ctx, T₀, T₁)`, interacts with both clients during
   issuance and `preRounds` adaptive pre-challenge spends, and then interacts with challenge thread
   `b : Bool` for `challengeSpends` rounds. Both `balancePartitionInitAdversary` (`T₀ ≠ T₁`) and
   `balancePartitionRefundAdversary` (`T₀ = T₁`, distinct pre-challenge refunds `x'₀ ≠ x'₁`) break
   `unguardedUnlinkabilityExperiment` with `Game.advantage = 1`, while the cross-branch non-abort
   guard in `unlinkabilityExperiment` collapses both attacks to `Game.advantage = 0`.
3. **Black-box adaptive unlinkability reduction (`unlinkabilityExperiment_advantage_le`)**:
   constructing explicit query-bounded ZK distinguisher `zkDistinguisher` (`≤ 2 + preRounds +
   challengeSpends` queries) and `TwoStage` hiding reduction `unlinkHidingReduction`, proving
   `Adv^unlink ≤ 2 * Adv^ZK + 2 * (2 + preRounds + challengeSpends) * Adv^hide` (original to
   this library; `[VOLEACT2026]` `#proof-status` leaves the unlinkability proof open). Here the
   leading factor of `2` arises from `Game.advantage_le_two_mul_uniform_bool_xor` in the library's
   `[0, 1]` two-world advantage convention, and all `2 + preRounds + challengeSpends` emitted
   commitments (reducing to `2 + challengeSpends` when `preRounds = 0`) are replaced sequentially
   because `choosePre` chooses client branches adaptively.

Non-black-box `G8 → G8.5` CRT witness-reuse decoupling lives in
`CslibFrontier.Crypto.Protocols.AnonymousToken.CRTDecoupling`. As in `CRTHazard.lean` and
`CRTDecoupling.lean`, all games and reductions here are finite query-bounded constructions
(`#7068`); asymptotic polynomial-time certificates are outside this module's scope.

## Main definitions

* `OpeningCommitment`, `OpeningCommitment.toScheme`: deterministic-evaluation opening commitment.
* `CommitMsg`, `CommitMsg.bumpBal`, `IssueStmt`, `IssueWit`, `SpendStmt`, `SpendWit`,
  `ProofStatement`, `ProofWitness`, `validStatement`, `ProverSystem`, `multiProofZKRealGame`,
  `multiProofZKSimGame`.
* `UnlinkAdversary`, `unlinkabilityExperiment`, `unguardedUnlinkabilityExperiment`.
* `balancePartitionInitAdversary`, `balancePartitionRefundAdversary`.
* `zkDistinguisher`, `unlinkHidingReduction`.

## Main results

* `OpeningCommitment.toScheme_correct`, `CommitMsg.bumpBal_ne`.
* `balancePartitionInit_unguarded_advantage_eq_one`,
  `balancePartitionInit_guarded_advantage_eq_zero`,
  `balancePartitionRefund_unguarded_advantage_eq_one`,
  `balancePartitionRefund_guarded_advantage_eq_zero`.
* `zkDistinguisher_isQueryBounded`, `unlinkabilityExperiment_advantage_le`.

## References

* [*VOLE-ACT*][VOLEACT2026], Protocol Specification / Initial Issuance (`#issuance`), Spending
  (`#spending`), and Proof Status (`#proof-status`).
-/

public section

namespace Cslib.Crypto.AnonymousToken.Unlinkability

open Probability
open Probability.PMF (uniformOfFintype uniformOfFintype_apply uniformOfFintype_map_equiv
  uniformOfFintype_prod)
open scoped ENNReal NNReal

/-- Congruence on the right branch of `PMF.bind`, keeping the continuation inside `PMF` instead of
unfolding to pointwise equality on `PMF` values. -/
private lemma pmfBind_congr {α β : Type} (p : PMF α) {f g : α → PMF β}
    (h : ∀ x, f x = g x) : p.bind f = p.bind g :=
  congrArg (PMF.bind p) (funext h)

section Protocol

/-- A commitment scheme whose evaluation algorithm `eval ck m r` is a deterministic function of
the commitment key, message, and sampled opening randomness `r ← openSample`. -/
structure OpeningCommitment (CommitKey Message Commitment Opening : Type) where
  /-- Key generation algorithm outputting a public commitment key. -/
  keyGen : ProbComp CommitKey
  /-- Opening-randomness sampler. -/
  openSample : ProbComp Opening
  /-- Deterministic commitment evaluation from key, message, and opening. -/
  eval : CommitKey → Message → Opening → Commitment

/-- Package an `OpeningCommitment` as a `Commitment.Scheme`. -/
@[expose] def OpeningCommitment.toScheme {CommitKey Message C Opening : Type}
    [DecidableEq C] (Com : OpeningCommitment CommitKey Message C Opening) :
    Commitment.Scheme CommitKey Message C Opening where
  keyGen := Com.keyGen
  commit ck m := do
    let r ← Com.openSample
    return (Com.eval ck m r, r)
  verify ck m c r := decide (Com.eval ck m r = c)

/-- Every honest opening emitted by `Com.toScheme.commit` passes `Com.toScheme.verify`. -/
theorem OpeningCommitment.toScheme_correct {CommitKey Message C Opening : Type}
    [DecidableEq C] (Com : OpeningCommitment CommitKey Message C Opening) :
    Com.toScheme.Correct := by
  intro ck _ m c r hmem
  simp only [OpeningCommitment.toScheme, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
  rcases hmem with ⟨r', _, heq⟩
  injection heq with hc hr
  subst c r'
  simp [OpeningCommitment.toScheme]

/-- Message committed inside a VOLE-ACT note commitment `Com(nf, ctx, t, r)`. -/
structure CommitMsg (Nullifier Context : Type) where
  /-- Note nullifier `nf`. -/
  nf : Nullifier
  /-- Issuance context `ctx`. -/
  ctx : Context
  /-- Note credit balance `t`. -/
  bal : ℕ
  deriving DecidableEq

/-- Distinct message obtained by incrementing the note balance by `1`, used in binding
reductions where two distinct messages must be committed to check collisions. -/
@[expose] def CommitMsg.bumpBal {Nullifier Context : Type} (m : CommitMsg Nullifier Context) :
    CommitMsg Nullifier Context :=
  ⟨m.nf, m.ctx, m.bal + 1⟩

/-- `CommitMsg.bumpBal` is always distinct from the original message. -/
theorem CommitMsg.bumpBal_ne {Nullifier Context : Type} (m : CommitMsg Nullifier Context) :
    m.bumpBal ≠ m := by
  intro h
  have hb : m.bal + 1 = m.bal := congrArg CommitMsg.bal h
  omega

/-- Public statement for a VOLE-ACT initial issuance proof ([VOLEACT2026], `#issuance`). -/
structure IssueStmt (C Context : Type) where
  /-- Issuance context `ctx`. -/
  ctx : Context
  /-- Token commitment `c`. -/
  c : C
  /-- Agreed initial balance `T`. -/
  t : ℕ
  deriving DecidableEq

/-- Secret witness for initial issuance `(nf, r)` ([VOLEACT2026], `#issuance`). -/
structure IssueWit (Nullifier O : Type) where
  /-- Note nullifier `nf`. -/
  nf : Nullifier
  /-- Commitment opening randomness `r`. -/
  r : O

/-- Public statement for a VOLE-ACT spend proof ([VOLEACT2026], `#spending`). -/
structure SpendStmt (PK C Context Nullifier : Type) where
  /-- Issuer verification key `pk`. -/
  pk : PK
  /-- Context `ctx`. -/
  ctx : Context
  /-- Revealed nullifier `nf` of the spent token. -/
  nf : Nullifier
  /-- Public debit amount `d`. -/
  d : ℕ
  /-- Change token commitment `c'`. -/
  cPrime : C
  deriving DecidableEq

/-- Secret witness for spending `(t, r, x, s, nf', t', r')` ([VOLEACT2026], `#spending`). -/
structure SpendWit (O Sig Nullifier : Type) where
  /-- Input token balance `t`. -/
  t : ℕ
  /-- Input commitment opening `r`. -/
  r : O
  /-- Input prior refund `x` (`0` after initial issuance). -/
  x : ℕ
  /-- Issuer signature `s` on `Tag(Com(nf, ctx, t, r), x)`. -/
  s : Sig
  /-- Fresh change nullifier `nf'`. -/
  nfPrime : Nullifier
  /-- Updated change balance `t'`. -/
  tPrime : ℕ
  /-- Change commitment opening `r'`. -/
  rPrime : O

/-- Combined proof statement for either initial issuance or spending. -/
inductive ProofStatement (PK C Context Nullifier : Type) where
  /-- Initial issuance statement. -/
  | issue (st : IssueStmt C Context)
  /-- Spend statement. -/
  | spend (st : SpendStmt PK C Context Nullifier)

/-- Combined proof witness for either initial issuance or spending. -/
inductive ProofWitness (O Sig Nullifier : Type) where
  /-- Initial issuance witness. -/
  | issue (w : IssueWit Nullifier O)
  /-- Spend witness. -/
  | spend (w : SpendWit O Sig Nullifier)

/-- Query passed to the multi-instance ZK proof oracle. -/
structure ProofQuery (PK C Context Nullifier O Sig : Type) where
  /-- Public proof statement. -/
  stmt : ProofStatement PK C Context Nullifier
  /-- Prover's private witness. -/
  wit : ProofWitness O Sig Nullifier

/-- Oracle specification returning `some π` on valid statements and `none` otherwise. -/
abbrev ProofSpec (PK C Context Nullifier O Sig Proof : Type) :
    OracleSpec (ProofQuery PK C Context Nullifier O Sig) :=
  fun _ => Option Proof

/-- Boolean statement-witness relation enforcing `(V1)`–`(V4)` and issuance range `0 < T < bound`
([VOLEACT2026], `#issuance` and `#spending`). -/
@[expose] def validStatement {CommitKey PK C Context Nullifier O Sig Target SK : Type}
    [DecidableEq C]
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (ck : CommitKey) :
    ProofStatement PK C Context Nullifier → ProofWitness O Sig Nullifier → Bool
  | .issue st, .issue w =>
    decide (0 < st.t ∧ st.t < bound ∧ Com.eval ck ⟨w.nf, st.ctx, st.t⟩ w.r = st.c)
  | .spend st, .spend w =>
    let oldCom := Com.eval ck ⟨st.nf, st.ctx, w.t⟩ w.r
    let newCom := Com.eval ck ⟨w.nfPrime, st.ctx, w.tPrime⟩ w.rPrime
    S.verify st.pk (tag oldCom w.x) w.s &&
      decide (newCom = st.cPrime ∧ st.d ≤ w.t + w.x ∧ w.tPrime = w.t + w.x - st.d ∧
        w.t < bound ∧ w.x < bound ∧ w.tPrime < bound ∧ st.d < bound)
  | _, _ => false

/-- Prover and simulator pair for the VOLE-ACT issuance/spend ZK proof system. -/
structure ProverSystem (CommitKey PK C Context Nullifier O Sig Proof : Type) where
  /-- Real prover algorithm taking commitment key, statement, and witness. -/
  prove : CommitKey → ProofStatement PK C Context Nullifier →
    ProofWitness O Sig Nullifier → ProbComp Proof
  /-- Zero-knowledge simulator taking only commitment key and public statement. -/
  simulate : CommitKey → ProofStatement PK C Context Nullifier → ProbComp Proof

section MultiZK

variable {CommitKey PK C Context Nullifier O Sig Target SK Proof : Type}
variable [DecidableEq C]

/-- Real multi-instance ZK oracle returning `none` when `validStatement = false` and running
`sys.prove` otherwise. -/
@[expose] def realProofOracle
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof) (ck : CommitKey)
    (q : ProofQuery PK C Context Nullifier O Sig) : ProbComp (Option Proof) :=
  if validStatement Com tag S bound ck q.stmt q.wit then
    some <$> sys.prove ck q.stmt q.wit
  else
    pure none

/-- Simulated multi-instance ZK oracle returning `none` when `validStatement = false` and running
`sys.simulate` on the statement alone otherwise. -/
def simProofOracle
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof) (ck : CommitKey)
    (q : ProofQuery PK C Context Nullifier O Sig) : ProbComp (Option Proof) :=
  if validStatement Com tag S bound ck q.stmt q.wit then
    some <$> sys.simulate ck q.stmt
  else
    pure none

/-- Real multi-instance ZK distinguishing game. -/
noncomputable def multiProofZKRealGame
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (dist : CommitKey → ProbOracleComp (ProofSpec PK C Context Nullifier O Sig Proof) Bool) :
    Game :=
  ProbComp.eval do
    let ck ← Com.keyGen
    (dist ck).run (realProofOracle Com tag S bound sys ck)

/-- Simulated multi-instance ZK distinguishing game. -/
noncomputable def multiProofZKSimGame
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (dist : CommitKey → ProbOracleComp (ProofSpec PK C Context Nullifier O Sig Proof) Bool) :
    Game :=
  ProbComp.eval do
    let ck ← Com.keyGen
    (dist ck).run (simProofOracle Com tag S bound sys ck)

end MultiZK

end Protocol

section UnlinkabilityGame

/-- Client note state maintained across issuance and spends. -/
structure ClientNote (Nullifier C O Sig : Type) where
  /-- Current note nullifier. -/
  nf : Nullifier
  /-- Current note balance `t`. -/
  bal : ℕ
  /-- Current opening randomness `r`. -/
  r : O
  /-- Current commitment `c`. -/
  com : C
  /-- Prior issuer refund `x` (`0` immediately after issuance). -/
  ref : ℕ
  /-- Issuer signature `s` on `Tag(c, ref)`. -/
  sig : Sig

/-- Adversary response to the initial setup query `init ck`. -/
structure InitOutput (PK Context State : Type) where
  /-- Maliciously chosen issuer public key `pk`. -/
  pk : PK
  /-- Chosen issuance context `ctx`. -/
  ctx : Context
  /-- Initial balance `T₀` agreed for client `0`. -/
  t0 : ℕ
  /-- Initial balance `T₁` agreed for client `1`. -/
  t1 : ℕ
  /-- Adversary state carried into issuance. -/
  st : State

/-- Adversary response finalizing both client issuances with `(s₀, s₁)`. -/
structure IssueResp (Sig State : Type) where
  /-- Signature on client `0`'s initial token commitment. -/
  s0 : Sig
  /-- Signature on client `1`'s initial token commitment. -/
  s1 : Sig
  /-- Updated adversary state. -/
  st : State

/-- Adversary pre-challenge spend command selecting client `0` or `1` and debit `d`. -/
structure PreSpendChoice (State : Type) where
  /-- Target client (`false` for `0`, `true` for `1`). -/
  client : Bool
  /-- Requested debit amount `d`. -/
  debit : ℕ
  /-- Updated adversary state. -/
  st : State

/-- Adversary response finalizing a spend with refund `x'` and signature `s'`. -/
structure SpendResp (Sig State : Type) where
  /-- Refund amount `x'` chosen by the issuer. -/
  refund : ℕ
  /-- Signature `s'` on `Tag(c', x')`. -/
  sig : Sig
  /-- Updated adversary state. -/
  st : State

/-- Adversary challenge-phase spend command choosing debit `d`. -/
structure ChallengeChoice (State : Type) where
  /-- Requested debit amount `d`. -/
  debit : ℕ
  /-- Updated adversary state. -/
  st : State

/-- Adaptive malicious-issuer unlinkability adversary choosing `(pk, ctx, T₀, T₁)`, signing
both client issuances, issuing `preRounds` adaptive pre-challenge spends on chosen clients,
executing `challengeSpends` adaptive challenge-thread spends, and guessing the challenge bit. -/
structure UnlinkAdversary
    (CommitKey PK Context C Nullifier Proof Sig State : Type)
    (preRounds challengeSpends : ℕ) where
  /-- Setup choice `(pk, ctx, T₀, T₁)` given commitment key `ck`. -/
  init : CommitKey → ProbComp (InitOutput PK Context State)
  /-- FinalizeIssue response given `(c₀, π₀)` and `(c₁, π₁)`. -/
  issue : State → C → Proof → C → Proof → ProbComp (IssueResp Sig State)
  /-- Select client (`false` = `0`, `true` = `1`) and debit for pre-challenge round `i`. -/
  choosePre : Fin preRounds → State → ProbComp (PreSpendChoice State)
  /-- FinalizeSpend response in pre-challenge round `i` on `(nf, d, c', π')`. -/
  finalizePre : Fin preRounds → State → Nullifier → ℕ → C → Proof →
    ProbComp (SpendResp Sig State)
  /-- Choose debit for challenge spend round `j`. -/
  chooseChallenge : Fin challengeSpends → State → ProbComp (ChallengeChoice State)
  /-- FinalizeSpend response in challenge spend round `j` on `(nf, d, c', π')`. -/
  finalizeChallenge : Fin challengeSpends → State → Nullifier → ℕ → C → Proof →
    ProbComp (SpendResp Sig State)
  /-- Final challenge-bit guess `b' : Bool`. -/
  guess : State → ProbComp Bool

variable {CommitKey PK C Context Nullifier O Sig Target SK Proof State : Type}
variable [DecidableEq C]

/-- Non-abort range admissibility test for spending a note with balance/refund `(bal, ref)`
on debit `d`: requires `d ≤ bal + ref`, `d < bound`, and `bal + ref - d < bound`. -/
@[expose] def spendAdmissible (bound bal ref d : ℕ) : Bool :=
  decide (d < bound ∧ d ≤ bal + ref ∧ bal + ref - d < bound)

/-- Minimal simulator note state tracking only `(nf, bal, ref)`, without commitment openings or
signatures (used by simulator hybrids and `TwoStage` hiding reductions). -/
structure SimNote (Nullifier : Type) where
  /-- Current note nullifier. -/
  nf : Nullifier
  /-- Current note credit balance. -/
  bal : ℕ
  /-- Current note refund value. -/
  ref : ℕ

/-- Project a full `ClientNote` to its simulator note state `(nf, bal, ref)`. -/
private def ClientNote.toSim {Nullifier C O Sig : Type}
    (n : ClientNote Nullifier C O Sig) : SimNote Nullifier :=
  ⟨n.nf, n.bal, n.ref⟩

/-- Resumable continuation point right before commitment slot `idx` is evaluated into `cStar`. -/
inductive SimContinuation
    (PK Context C Nullifier Proof State : Type) (preRounds challengeSpends : ℕ) where
  /-- Paused immediately before client `0` initial issuance commitment. -/
  | issue0 (b : Bool) (pk : PK) (ctx : Context) (t0 t1 : ℕ) (st : State) (nf0 : Nullifier)
  /-- Paused immediately before client `1` initial issuance commitment. -/
  | issue1 (b : Bool) (pk : PK) (ctx : Context) (t0 t1 : ℕ) (st : State)
      (nf0 : Nullifier) (c0 : C) (pi0 : Proof) (nf1 : Nullifier)
  /-- Paused immediately before pre-challenge spend `i` commitment. -/
  | pre (b : Bool) (pk : PK) (ctx : Context) (note0 note1 : SimNote Nullifier)
      (cClient : Bool) (d : ℕ) (st : State) (nfPrime : Nullifier) (tPrime : ℕ)
      (i : ℕ) (hi : i < preRounds)
  /-- Paused immediately before challenge-phase spend `j` commitment. -/
  | chal (pk : PK) (ctx : Context) (noteAct : SimNote Nullifier)
      (balOther refOther : ℕ) (st : State) (d : ℕ) (nfPrime : Nullifier) (tPrime : ℕ)
      (j : ℕ) (hj : j < challengeSpends)
  /-- Execution already terminated with final output `res`. -/
  | done (res : Bool)

/-- Output of running the simulator hybrid until pause slot `pauseSlot`. -/
private structure PauseResult
    (PK Context C Nullifier Proof State : Type) (preRounds challengeSpends : ℕ) where
  /-- Real note message submitted as left hiding challenge. -/
  msgReal : CommitMsg Nullifier Context
  /-- Dummy note message submitted as right hiding challenge. -/
  msgDummy : CommitMsg Nullifier Context
  /-- Continuation resuming execution after receiving challenge commitment `cStar`. -/
  cont : SimContinuation PK Context C Nullifier Proof State preRounds challengeSpends

section UnlinkPrograms

/-- Challenge-spend loop inside `ProbOracleComp (ProofSpec ...) Bool`. -/
@[expose] def challengeLoopOracle
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (ck : CommitKey) (pk : PK) (ctx : Context) (guardBoth : Bool)
    (rem : ℕ) (hrem : rem ≤ challengeSpends)
    (noteAct : ClientNote Nullifier C O Sig) (balOther refOther : ℕ) (st : State) :
    ProbOracleComp (ProofSpec PK C Context Nullifier O Sig Proof) Bool :=
  match rem with
  | 0 => ProbOracleComp.sample (adv.guess st)
  | rem' + 1 =>
    let j : Fin challengeSpends := ⟨challengeSpends - (rem' + 1), by omega⟩
    do
      let choice ← ProbOracleComp.sample (adv.chooseChallenge j st)
      let okAct := spendAdmissible bound noteAct.bal noteAct.ref choice.debit
      let okOther := spendAdmissible bound balOther refOther choice.debit
      if !(okAct && (!guardBoth || okOther)) then
        return false
      else
        let nfPrime ← ProbOracleComp.sample nfGen
        let rPrime ← ProbOracleComp.sample Com.openSample
        let tPrime := noteAct.bal + noteAct.ref - choice.debit
        let cPrime := Com.eval ck ⟨nfPrime, ctx, tPrime⟩ rPrime
        let stmt : ProofStatement PK C Context Nullifier :=
          .spend ⟨pk, ctx, noteAct.nf, choice.debit, cPrime⟩
        let wit : ProofWitness O Sig Nullifier :=
          .spend ⟨noteAct.bal, noteAct.r, noteAct.ref, noteAct.sig, nfPrime, tPrime, rPrime⟩
        let pi? ← ProbOracleComp.query ⟨stmt, wit⟩
        match pi? with
        | none => return false
        | some pi =>
          let resp ← ProbOracleComp.sample
            (adv.finalizeChallenge j choice.st noteAct.nf choice.debit cPrime pi)
          if !(resp.refund < bound && S.verify pk (tag cPrime resp.refund) resp.sig) then
            return false
          else
            let noteNext : ClientNote Nullifier C O Sig :=
              ⟨nfPrime, tPrime, rPrime, cPrime, resp.refund, resp.sig⟩
            let balOtherNext := balOther + refOther - choice.debit
            challengeLoopOracle Com nfGen tag S bound adv ck pk ctx guardBoth rem' (by omega)
              noteNext balOtherNext resp.refund resp.st

/-- Adaptive pre-challenge spend loop inside `ProbOracleComp (ProofSpec ...) Bool`, transitioning
into `challengeLoopOracle` once all `preRounds` complete. -/
@[expose] def preLoopOracle
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (ck : CommitKey) (pk : PK) (ctx : Context) (guardBoth b : Bool)
    (rem : ℕ) (hrem : rem ≤ preRounds)
    (note0 note1 : ClientNote Nullifier C O Sig) (st : State) :
    ProbOracleComp (ProofSpec PK C Context Nullifier O Sig Proof) Bool :=
  match rem with
  | 0 =>
    if b then
      challengeLoopOracle Com nfGen tag S bound adv ck pk ctx guardBoth
        challengeSpends (le_refl _) note1 note0.bal note0.ref st
    else
      challengeLoopOracle Com nfGen tag S bound adv ck pk ctx guardBoth
        challengeSpends (le_refl _) note0 note1.bal note1.ref st
  | rem' + 1 =>
    let i : Fin preRounds := ⟨preRounds - (rem' + 1), by omega⟩
    do
      let choice ← ProbOracleComp.sample (adv.choosePre i st)
      let noteSel := if choice.client then note1 else note0
      if !spendAdmissible bound noteSel.bal noteSel.ref choice.debit then
        return false
      else
        let nfPrime ← ProbOracleComp.sample nfGen
        let rPrime ← ProbOracleComp.sample Com.openSample
        let tPrime := noteSel.bal + noteSel.ref - choice.debit
        let cPrime := Com.eval ck ⟨nfPrime, ctx, tPrime⟩ rPrime
        let stmt : ProofStatement PK C Context Nullifier :=
          .spend ⟨pk, ctx, noteSel.nf, choice.debit, cPrime⟩
        let wit : ProofWitness O Sig Nullifier :=
          .spend ⟨noteSel.bal, noteSel.r, noteSel.ref, noteSel.sig, nfPrime, tPrime, rPrime⟩
        let pi? ← ProbOracleComp.query ⟨stmt, wit⟩
        match pi? with
        | none => return false
        | some pi =>
          let resp ← ProbOracleComp.sample
            (adv.finalizePre i choice.st noteSel.nf choice.debit cPrime pi)
          if !(resp.refund < bound && S.verify pk (tag cPrime resp.refund) resp.sig) then
            return false
          else
            let noteUpdated : ClientNote Nullifier C O Sig :=
              ⟨nfPrime, tPrime, rPrime, cPrime, resp.refund, resp.sig⟩
            let note0' := if choice.client then note0 else noteUpdated
            let note1' := if choice.client then noteUpdated else note1
            preLoopOracle Com nfGen tag S bound adv ck pk ctx guardBoth b rem' (by omega)
              note0' note1' resp.st

/-- Oracle-based adaptive unlinkability program queried against `ProofOracle`. -/
@[expose] def unlinkOracleProgram
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (guardBoth b : Bool) (ck : CommitKey) :
    ProbOracleComp (ProofSpec PK C Context Nullifier O Sig Proof) Bool := do
  let initOut ← ProbOracleComp.sample (adv.init ck)
  if !(0 < initOut.t0 && initOut.t0 < bound && 0 < initOut.t1 && initOut.t1 < bound) then
    return false
  else
    let nf0 ← ProbOracleComp.sample nfGen
    let r0 ← ProbOracleComp.sample Com.openSample
    let c0 := Com.eval ck ⟨nf0, initOut.ctx, initOut.t0⟩ r0
    let pi0? ← ProbOracleComp.query ⟨.issue ⟨initOut.ctx, c0, initOut.t0⟩, .issue ⟨nf0, r0⟩⟩
    match pi0? with
    | none => return false
    | some pi0 =>
      let nf1 ← ProbOracleComp.sample nfGen
      let r1 ← ProbOracleComp.sample Com.openSample
      let c1 := Com.eval ck ⟨nf1, initOut.ctx, initOut.t1⟩ r1
      let pi1? ← ProbOracleComp.query ⟨.issue ⟨initOut.ctx, c1, initOut.t1⟩, .issue ⟨nf1, r1⟩⟩
      match pi1? with
      | none => return false
      | some pi1 =>
        let issResp ← ProbOracleComp.sample (adv.issue initOut.st c0 pi0 c1 pi1)
        if !(S.verify initOut.pk (tag c0 0) issResp.s0 &&
            S.verify initOut.pk (tag c1 0) issResp.s1) then
          return false
        else
          let note0 : ClientNote Nullifier C O Sig :=
            ⟨nf0, initOut.t0, r0, c0, 0, issResp.s0⟩
          let note1 : ClientNote Nullifier C O Sig :=
            ⟨nf1, initOut.t1, r1, c1, 0, issResp.s1⟩
          preLoopOracle Com nfGen tag S bound adv ck initOut.pk initOut.ctx guardBoth b
            preRounds (le_refl _) note0 note1 issResp.st

/-- Guarded adaptive malicious-issuer unlinkability experiment (`guardBoth = true`, cross-branch
non-abort check enforced). -/
@[expose] noncomputable def unlinkabilityExperiment
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (b : Bool) : Game :=
  ProbComp.eval do
    let ck ← Com.keyGen
    (unlinkOracleProgram Com nfGen tag S bound adv true b ck).run
      (realProofOracle Com tag S bound sys ck)

/-- Unguarded adaptive malicious-issuer unlinkability experiment (`guardBoth = false`, active-branch
abort check only, exposing balance-partitioning attacks). -/
noncomputable def unguardedUnlinkabilityExperiment
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (b : Bool) : Game :=
  ProbComp.eval do
    let ck ← Com.keyGen
    (unlinkOracleProgram Com nfGen tag S bound adv false b ck).run
      (realProofOracle Com tag S bound sys ck)

end UnlinkPrograms

section BalancePartitionAttacks

/-- Negative balance-partitioning adversary with distinct initial balances `T₀ = 2`, `T₁ = 1`
and `preRounds = 0`: requests challenge debit `d = 2`, succeeding only when `b = false`. -/
def balancePartitionInitAdversary (tag : C → ℕ → Target) (pk : PK) (ctx : Context)
    (mkSig : Target → Sig) :
    UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig Unit 0 1 where
  init _ := pure ⟨pk, ctx, 2, 1, ()⟩
  issue _ c0 _ c1 _ := pure ⟨mkSig (tag c0 0), mkSig (tag c1 0), ()⟩
  choosePre i _ := Fin.elim0 i
  finalizePre i _ _ _ _ _ := Fin.elim0 i
  chooseChallenge _ _ := pure ⟨2, ()⟩
  finalizeChallenge _ _ _ _ cPrime _ := pure ⟨0, mkSig (tag cPrime 0), ()⟩
  guess _ := pure true

/-- Shared helper collapsing a valid `realProofOracle` query bind into `sys.prove` at `PMF`
level. -/
private lemma bind_realProofOracle_valid
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    {stmt : ProofStatement PK C Context Nullifier} {wit : ProofWitness O Sig Nullifier}
    (ck : CommitKey)
    (hval : validStatement Com tag S bound ck stmt wit = true)
    (k : Option Proof → PMF Bool) :
    (ProbComp.eval (realProofOracle Com tag S bound sys ck ⟨stmt, wit⟩)).bind k =
    (ProbComp.eval (sys.prove ck stmt wit)).bind fun pi => k (some pi) := by
  simp only [realProofOracle, hval, ↓reduceIte, ProbComp.eval_map, PMF.bind_map, Function.comp_def]

/-- Shared issuance-phase reduction for any deterministic `mkSig` balance-partitioning adversary
issuing initial balances `(t0, t1)` (`0 < t0 < bound`, `0 < t1 < bound`). -/
private lemma eval_unlinkOracleProgram_mkSig_issue
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig Unit
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (t0 t1 : ℕ) (mkSig : Target → Sig)
    (ht0 : 0 < t0 ∧ t0 < bound) (ht1 : 0 < t1 ∧ t1 < bound)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true)
    (hinit : ∀ ck, adv.init ck = pure ⟨pk, ctx, t0, t1, ()⟩)
    (hissue : ∀ st c0 pi0 c1 pi1,
      adv.issue st c0 pi0 c1 pi1 = pure ⟨mkSig (tag c0 0), mkSig (tag c1 0), ()⟩)
    (guardBoth b : Bool) (ck : CommitKey) :
    ProbComp.eval ((unlinkOracleProgram Com nfGen tag S bound adv guardBoth b ck).run
        (realProofOracle Com tag S bound sys ck)) =
      (ProbComp.eval nfGen).bind fun nf0 =>
      (ProbComp.eval Com.openSample).bind fun r0 =>
      (ProbComp.eval (sys.prove ck
        (.issue ⟨ctx, Com.eval ck ⟨nf0, ctx, t0⟩ r0, t0⟩) (.issue ⟨nf0, r0⟩))).bind fun _ =>
      (ProbComp.eval nfGen).bind fun nf1 =>
      (ProbComp.eval Com.openSample).bind fun r1 =>
      (ProbComp.eval (sys.prove ck
        (.issue ⟨ctx, Com.eval ck ⟨nf1, ctx, t1⟩ r1, t1⟩) (.issue ⟨nf1, r1⟩))).bind fun _ =>
      ProbComp.eval ((preLoopOracle Com nfGen tag S bound adv ck pk ctx guardBoth b preRounds
        (le_refl _)
        ⟨nf0, t0, r0, Com.eval ck ⟨nf0, ctx, t0⟩ r0, 0,
          mkSig (tag (Com.eval ck ⟨nf0, ctx, t0⟩ r0) 0)⟩
        ⟨nf1, t1, r1, Com.eval ck ⟨nf1, ctx, t1⟩ r1, 0,
          mkSig (tag (Com.eval ck ⟨nf1, ctx, t1⟩ r1) 0)⟩
        ()).run (realProofOracle Com tag S bound sys ck)) := by
  simp only [unlinkOracleProgram, hinit, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
  have hcond : (0 < t0 && t0 < bound && 0 < t1 && t1 < bound) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨ht0.1, ht0.2⟩, ht1.1⟩, ht1.2⟩
  simp only [hcond, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbOracleComp.run_query, ProbComp.eval_bind]
  refine pmfBind_congr _ fun nf0 => pmfBind_congr _ fun r0 => ?_
  have hv0 : validStatement Com tag S bound ck
      (.issue ⟨ctx, Com.eval ck ⟨nf0, ctx, t0⟩ r0, t0⟩) (.issue ⟨nf0, r0⟩) = true := by
    simp [validStatement, ht0.1, ht0.2]
  rw [bind_realProofOracle_valid Com tag S bound sys ck hv0]
  dsimp only
  refine pmfBind_congr _ fun pi0 => ?_
  simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_query,
    ProbComp.eval_bind]
  refine pmfBind_congr _ fun nf1 => pmfBind_congr _ fun r1 => ?_
  have hv1 : validStatement Com tag S bound ck
      (.issue ⟨ctx, Com.eval ck ⟨nf1, ctx, t1⟩ r1, t1⟩) (.issue ⟨nf1, r1⟩) = true := by
    simp [validStatement, ht1.1, ht1.2]
  rw [bind_realProofOracle_valid Com tag S bound sys ck hv1]
  dsimp only
  refine pmfBind_congr _ fun pi1 => ?_
  simp only [hissue, ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.pure_bind, hmksig, Bool.and_self, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]

/-- Helper evaluating a single-round `challengeLoopOracle` when `chooseChallenge 0` requests
debit `2`, `finalizeChallenge 0` grants refund `0`, `guess` returns `true`, and `balAct + refAct`
equals `2` (respecting the cross-branch guard when enabled). -/
private lemma eval_challengeLoop_debit2_true
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    {preRounds : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig Unit preRounds 1)
    (hbound : 3 ≤ bound) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true)
    (hchoose : ∀ st, adv.chooseChallenge 0 st = pure ⟨2, ()⟩)
    (hfin : ∀ st nf d cPrime pi,
      adv.finalizeChallenge 0 st nf d cPrime pi = pure ⟨0, mkSig (tag cPrime 0), ()⟩)
    (hguess : ∀ st, adv.guess st = pure true)
    (ck : CommitKey) (guardBoth : Bool)
    (noteAct : ClientNote Nullifier C O Sig) (balOther refOther : ℕ)
    (hsum : 2 ≤ noteAct.bal + noteAct.ref ∧ noteAct.bal + noteAct.ref - 2 < bound)
    (hoth : guardBoth = true → 2 ≤ balOther + refOther ∧ balOther + refOther - 2 < bound)
    (hnote_com : noteAct.com = Com.eval ck ⟨noteAct.nf, ctx, noteAct.bal⟩ noteAct.r)
    (hnote_bal : noteAct.bal < bound) (hnote_ref : noteAct.ref < bound)
    (hnote_sig : S.verify pk (tag noteAct.com noteAct.ref) noteAct.sig = true) :
    ProbComp.eval ((challengeLoopOracle Com nfGen tag S bound adv ck pk ctx guardBoth 1
        (le_refl _) noteAct balOther refOther ()).run (realProofOracle Com tag S bound sys ck)) =
      (ProbComp.eval nfGen).bind fun nfC =>
      (ProbComp.eval Com.openSample).bind fun rC =>
      (ProbComp.eval (sys.prove ck
        (.spend ⟨pk, ctx, noteAct.nf, 2, Com.eval ck ⟨nfC, ctx, noteAct.bal + noteAct.ref - 2⟩
          rC⟩)
        (.spend ⟨noteAct.bal, noteAct.r, noteAct.ref, noteAct.sig, nfC,
          noteAct.bal + noteAct.ref - 2, rC⟩))).bind fun _ =>
        PMF.pure true := by
  have hj0 : (⟨1 - (0 + 1), by omega⟩ : Fin 1) = 0 := rfl
  simp only [challengeLoopOracle, hj0, hchoose, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, spendAdmissible]
  have hadm1 : decide (2 < bound ∧ 2 ≤ noteAct.bal + noteAct.ref ∧
      noteAct.bal + noteAct.ref - 2 < bound) = true := by
    simp only [decide_eq_true_eq]
    exact ⟨by omega, by omega, by omega⟩
  have hadm2 : (!guardBoth || decide (2 < bound ∧ 2 ≤ balOther + refOther ∧
      balOther + refOther - 2 < bound)) = true := by
    cases guardBoth
    · rfl
    · have ho := hoth rfl
      simp [show 2 < bound by omega, ho.1, ho.2]
  simp only [hadm1, hadm2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_query,
    ProbComp.eval_bind]
  refine pmfBind_congr _ fun nfC => pmfBind_congr _ fun rC => ?_
  have hv : validStatement Com tag S bound ck
      (.spend ⟨pk, ctx, noteAct.nf, 2, Com.eval ck ⟨nfC, ctx, noteAct.bal + noteAct.ref - 2⟩
        rC⟩)
      (.spend ⟨noteAct.bal, noteAct.r, noteAct.ref, noteAct.sig, nfC,
        noteAct.bal + noteAct.ref - 2, rC⟩) = true := by
    simp only [validStatement, ← hnote_com, hnote_sig, Bool.true_and, decide_eq_true_eq]
    exact ⟨by simp, by omega, by simp, hnote_bal, hnote_ref, by omega, by omega⟩
  rw [bind_realProofOracle_valid Com tag S bound sys ck hv]
  dsimp only
  refine pmfBind_congr _ fun piC => ?_
  simp only [hfin, ProbOracleComp.run_sample, ProbOracleComp.run_bind, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.pure_bind, hmksig, show (0 : ℕ) < bound by omega, decide_true,
    Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hguess]

/-- Helper showing a `challengeLoopOracle` debit-`2` call aborts immediately (`PMF.pure false`)
whenever `balAct + refAct < 2` or `(guardBoth = true ∧ balOther + refOther < 2)`. -/
private lemma eval_challengeLoop_debit2_false
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    {preRounds : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig Unit preRounds 1)
    (hchoose : ∀ st, adv.chooseChallenge 0 st = pure ⟨2, ()⟩)
    (ck : CommitKey) (pk : PK) (ctx : Context) (guardBoth : Bool)
    (noteAct : ClientNote Nullifier C O Sig) (balOther refOther : ℕ)
    (habort : noteAct.bal + noteAct.ref < 2 ∨ (guardBoth = true ∧ balOther + refOther < 2)) :
    ProbComp.eval ((challengeLoopOracle Com nfGen tag S bound adv ck pk ctx guardBoth 1
        (le_refl _) noteAct balOther refOther ()).run (realProofOracle Com tag S bound sys ck)) =
      PMF.pure false := by
  have hj0 : (⟨1 - (0 + 1), by omega⟩ : Fin 1) = 0 := rfl
  simp only [challengeLoopOracle, hj0, hchoose, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, spendAdmissible]
  rcases habort with h1 | ⟨rfl, h2⟩
  · have hadm : decide (2 < bound ∧ 2 ≤ noteAct.bal + noteAct.ref ∧
        noteAct.bal + noteAct.ref - 2 < bound) = false := by
      simp only [decide_eq_false_iff_not]; omega
    simp [hadm]
  · have hadm : decide (2 < bound ∧ 2 ≤ balOther + refOther ∧
        balOther + refOther - 2 < bound) = false := by
      simp only [decide_eq_false_iff_not]; omega
    simp [hadm]

/-- Shared evaluation helper for `balancePartitionInitAdversary` across worlds. -/
private lemma eval_balancePartitionInit_eq
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (hbound : 3 ≤ bound) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true) (guardBoth b res : Bool)
    (htail : ∀ ck nf r,
      ProbComp.eval ((challengeLoopOracle Com nfGen tag S bound
        (balancePartitionInitAdversary tag pk ctx mkSig) ck pk ctx guardBoth 1 (le_refl _)
        ⟨nf, if b then 1 else 2, r, Com.eval ck ⟨nf, ctx, if b then 1 else 2⟩ r, 0,
          mkSig (tag (Com.eval ck ⟨nf, ctx, if b then 1 else 2⟩ r) 0)⟩
        (if b then 2 else 1) 0 ()).run (realProofOracle Com tag S bound sys ck)) =
      PMF.pure res) :
    ProbComp.eval (do
      let ck ← Com.keyGen
      (unlinkOracleProgram Com nfGen tag S bound
        (balancePartitionInitAdversary tag pk ctx mkSig) guardBoth b ck).run
        (realProofOracle Com tag S bound sys ck)) = PMF.pure res := by
  simp only [ProbComp.eval_bind]
  trans (ProbComp.eval Com.keyGen).bind fun _ => PMF.pure res
  · refine pmfBind_congr _ fun ck => ?_
    rw [eval_unlinkOracleProgram_mkSig_issue Com nfGen tag S bound sys _ pk ctx 2 1 mkSig
      (by omega) (by omega) hmksig (fun _ => rfl) (fun _ _ _ _ _ => rfl) guardBoth b ck]
    cases b <;>
    · simp only [preLoopOracle, Bool.false_eq_true, ↓reduceIte] at htail ⊢
      simp only [htail ck, PMF.bind_const]
  · simp only [PMF.bind_const]

private lemma eval_balancePartitionInit_abort
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (hbound : 3 ≤ bound) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true) (guardBoth b : Bool)
    (hbad : if b then True else guardBoth = true) :
    ProbComp.eval (do
      let ck ← Com.keyGen
      (unlinkOracleProgram Com nfGen tag S bound
        (balancePartitionInitAdversary tag pk ctx mkSig) guardBoth b ck).run
        (realProofOracle Com tag S bound sys ck)) = PMF.pure false := by
  refine eval_balancePartitionInit_eq Com nfGen tag S bound sys hbound pk ctx mkSig hmksig
    guardBoth b false fun ck nf r => ?_
  cases b
  · exact eval_challengeLoop_debit2_false Com nfGen tag S bound sys _ (fun _ => rfl) ck pk ctx
      guardBoth _ 1 0 (Or.inr ⟨hbad, by simp⟩)
  · exact eval_challengeLoop_debit2_false Com nfGen tag S bound sys _ (fun _ => rfl) ck pk ctx
      guardBoth _ 2 0 (Or.inl (by simp))

/-- Without the cross-branch non-abort guard, `balancePartitionInitAdversary` achieves
unlinkability advantage `1` whenever `bound ≥ 3` and `mkSig` produces valid signatures under
`pk`. -/
theorem balancePartitionInit_unguarded_advantage_eq_one
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (hbound : 3 ≤ bound) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true) :
    Game.advantage
      (unguardedUnlinkabilityExperiment Com nfGen tag S bound sys
        (balancePartitionInitAdversary tag pk ctx mkSig) false)
      (unguardedUnlinkabilityExperiment Com nfGen tag S bound sys
        (balancePartitionInitAdversary tag pk ctx mkSig) true) = 1 := by
  let adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig Unit 0 1 :=
    balancePartitionInitAdversary tag pk ctx mkSig
  have hfalse :
      unguardedUnlinkabilityExperiment Com nfGen tag S bound sys adv false = PMF.pure true := by
    refine eval_balancePartitionInit_eq Com nfGen tag S bound sys hbound pk ctx mkSig hmksig
      false false true fun ck nf0 r0 => ?_
    refine (eval_challengeLoop_debit2_true Com nfGen tag S bound sys adv hbound pk ctx mkSig
      hmksig (fun _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ => rfl) ck false
      ⟨nf0, 2, r0, Com.eval ck ⟨nf0, ctx, 2⟩ r0, 0,
        mkSig (tag (Com.eval ck ⟨nf0, ctx, 2⟩ r0) 0)⟩
      1 0 ⟨by dsimp; omega, by dsimp; omega⟩ (by intro h; cases h) rfl (by dsimp; omega)
      (by dsimp; omega) (hmksig _)).trans ?_
    simp only [PMF.bind_const]
  have htrue :
      unguardedUnlinkabilityExperiment Com nfGen tag S bound sys adv true = PMF.pure false :=
    eval_balancePartitionInit_abort Com nfGen tag S bound sys hbound pk ctx mkSig hmksig
      false true trivial
  rw [hfalse, htrue]
  exact NNReal.eq_iff.mpr (by simp [Game.coe_succProbability])

/-- With the cross-branch non-abort guard enabled, `balancePartitionInitAdversary` aborts
identically in both worlds and achieves unlinkability advantage `0`. -/
theorem balancePartitionInit_guarded_advantage_eq_zero
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (hbound : 3 ≤ bound) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true) :
    Game.advantage
      (unlinkabilityExperiment Com nfGen tag S bound sys
        (balancePartitionInitAdversary tag pk ctx mkSig) false)
      (unlinkabilityExperiment Com nfGen tag S bound sys
        (balancePartitionInitAdversary tag pk ctx mkSig) true) = 0 := by
  have hzero (b : Bool) :
      unlinkabilityExperiment Com nfGen tag S bound sys
        (balancePartitionInitAdversary tag pk ctx mkSig) b = PMF.pure false := by
    cases b
    · exact eval_balancePartitionInit_abort Com nfGen tag S bound sys hbound pk ctx mkSig hmksig
        true false rfl
    · exact eval_balancePartitionInit_abort Com nfGen tag S bound sys hbound pk ctx mkSig hmksig
        true true trivial
  rw [hzero false, hzero true, Game.advantage_self]

/-- Negative balance-partitioning adversary with equal initial balances `T₀ = T₁ = 2` and
`preRounds = 2`: pre-spend `0` gives client `0` refund `2` (`bal + ref = 3`), pre-spend `1` gives
client `1` refund `0` (`bal + ref = 1`), and challenge spend requests debit `2`. -/
def balancePartitionRefundAdversary (tag : C → ℕ → Target) (pk : PK) (ctx : Context)
    (mkSig : Target → Sig) :
    UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig Unit 2 1 where
  init _ := pure ⟨pk, ctx, 2, 2, ()⟩
  issue _ c0 _ c1 _ := pure ⟨mkSig (tag c0 0), mkSig (tag c1 0), ()⟩
  choosePre i _ := if i.val = 0 then pure ⟨false, 1, ()⟩ else pure ⟨true, 1, ()⟩
  finalizePre i _ _ _ cPrime _ :=
    if i.val = 0 then pure ⟨2, mkSig (tag cPrime 2), ()⟩
    else pure ⟨0, mkSig (tag cPrime 0), ()⟩
  chooseChallenge _ _ := pure ⟨2, ()⟩
  finalizeChallenge _ _ _ _ cPrime _ := pure ⟨0, mkSig (tag cPrime 0), ()⟩
  guess _ := pure true

private lemma spendValid_mkSig_note2
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (hbound : 5 ≤ bound) (ck : CommitKey) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true) (nf : Nullifier) (r : O)
    (nf' : Nullifier) (r' : O) :
    validStatement Com tag S bound ck
      (.spend ⟨pk, ctx, nf, 1, Com.eval ck ⟨nf', ctx, 1⟩ r'⟩)
      (.spend ⟨2, r, 0, mkSig (tag (Com.eval ck ⟨nf, ctx, 2⟩ r) 0), nf', 1, r'⟩) = true := by
  simp only [validStatement, hmksig, Bool.true_and, decide_eq_true_eq]
  exact ⟨by simp, by omega, by simp, by omega, by omega, by omega, by omega⟩

/-- Shared pre-challenge reduction for `balancePartitionRefundAdversary`: executes both `1`-debit
pre-spends and hands off the resulting notes (`bal0' + ref0' = 3`, `bal1' + ref1' = 1`) into the
challenge spend phase. -/
private lemma eval_refund_preLoopOracle
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (hbound : 5 ≤ bound) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true)
    (ck : CommitKey) (guardBoth b : Bool) (nf0 nf1 : Nullifier) (r0 r1 : O) :
    ProbComp.eval ((preLoopOracle Com nfGen tag S bound
        (balancePartitionRefundAdversary tag pk ctx mkSig) ck pk ctx guardBoth b 2 (by omega)
        ⟨nf0, 2, r0, Com.eval ck ⟨nf0, ctx, 2⟩ r0, 0,
          mkSig (tag (Com.eval ck ⟨nf0, ctx, 2⟩ r0) 0)⟩
        ⟨nf1, 2, r1, Com.eval ck ⟨nf1, ctx, 2⟩ r1, 0,
          mkSig (tag (Com.eval ck ⟨nf1, ctx, 2⟩ r1) 0)⟩ ()).run
        (realProofOracle Com tag S bound sys ck)) =
      (ProbComp.eval nfGen).bind fun nf0' =>
      (ProbComp.eval Com.openSample).bind fun r0' =>
      (ProbComp.eval (sys.prove ck (.spend ⟨pk, ctx, nf0, 1, Com.eval ck ⟨nf0', ctx, 1⟩ r0'⟩)
        (.spend ⟨2, r0, 0, mkSig (tag (Com.eval ck ⟨nf0, ctx, 2⟩ r0) 0), nf0', 1, r0'⟩))).bind
        fun _ =>
      (ProbComp.eval nfGen).bind fun nf1' =>
      (ProbComp.eval Com.openSample).bind fun r1' =>
      (ProbComp.eval (sys.prove ck (.spend ⟨pk, ctx, nf1, 1, Com.eval ck ⟨nf1', ctx, 1⟩ r1'⟩)
        (.spend ⟨2, r1, 0, mkSig (tag (Com.eval ck ⟨nf1, ctx, 2⟩ r1) 0), nf1', 1, r1'⟩))).bind
        fun _ =>
      ProbComp.eval ((preLoopOracle Com nfGen tag S bound
        (balancePartitionRefundAdversary tag pk ctx mkSig) ck pk ctx guardBoth b 0 (by omega)
        ⟨nf0', 1, r0', Com.eval ck ⟨nf0', ctx, 1⟩ r0', 2,
          mkSig (tag (Com.eval ck ⟨nf0', ctx, 1⟩ r0') 2)⟩
        ⟨nf1', 1, r1', Com.eval ck ⟨nf1', ctx, 1⟩ r1', 0,
          mkSig (tag (Com.eval ck ⟨nf1', ctx, 1⟩ r1') 0)⟩ ()).run
        (realProofOracle Com tag S bound sys ck)) := by
  simp only [preLoopOracle, balancePartitionRefundAdversary, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, ↓reduceIte,
    Bool.false_eq_true, spendAdmissible]
  have hadm0 : decide (1 < bound ∧ 1 ≤ 2 + 0 ∧ 2 + 0 - 1 < bound) = true := by
    simp only [decide_eq_true_eq]; omega
  simp only [hadm0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbOracleComp.run_query, ProbComp.eval_bind]
  refine pmfBind_congr _ fun nf0' => pmfBind_congr _ fun r0' => ?_
  rw [bind_realProofOracle_valid Com tag S bound sys ck
    (spendValid_mkSig_note2 Com tag S bound hbound ck pk ctx mkSig hmksig nf0 r0 nf0' r0')]
  dsimp only
  refine pmfBind_congr _ fun pi0' => ?_
  simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.pure_bind, hmksig, Bool.and_true, show (2 : ℕ) < bound by omega,
    decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have h1ne0 : ¬((2 - (0 + 1) : ℕ) = 0) := by omega
  simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.pure_bind, h1ne0, ↓reduceIte, hadm0, Bool.not_true, Bool.false_eq_true,
    ProbOracleComp.run_query]
  refine pmfBind_congr _ fun nf1' => pmfBind_congr _ fun r1' => ?_
  rw [bind_realProofOracle_valid Com tag S bound sys ck
    (spendValid_mkSig_note2 Com tag S bound hbound ck pk ctx mkSig hmksig nf1 r1 nf1' r1')]
  dsimp only
  refine pmfBind_congr _ fun pi1' => ?_
  simp [hmksig, show bound ≠ 0 by omega]

private lemma eval_balancePartitionRefund_eq
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (hbound : 5 ≤ bound) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true) (guardBoth b res : Bool)
    (hchal : ∀ ck nf0' r0' nf1' r1',
      ProbComp.eval ((preLoopOracle Com nfGen tag S bound
        (balancePartitionRefundAdversary tag pk ctx mkSig) ck pk ctx guardBoth b 0 (by omega)
        ⟨nf0', 1, r0', Com.eval ck ⟨nf0', ctx, 1⟩ r0', 2,
          mkSig (tag (Com.eval ck ⟨nf0', ctx, 1⟩ r0') 2)⟩
        ⟨nf1', 1, r1', Com.eval ck ⟨nf1', ctx, 1⟩ r1', 0,
          mkSig (tag (Com.eval ck ⟨nf1', ctx, 1⟩ r1') 0)⟩ ()).run
        (realProofOracle Com tag S bound sys ck)) = PMF.pure res) :
    ProbComp.eval (do
      let ck ← Com.keyGen
      (unlinkOracleProgram Com nfGen tag S bound
        (balancePartitionRefundAdversary tag pk ctx mkSig) guardBoth b ck).run
        (realProofOracle Com tag S bound sys ck)) = PMF.pure res := by
  simp only [ProbComp.eval_bind]
  trans (ProbComp.eval Com.keyGen).bind fun _ => PMF.pure res
  · refine pmfBind_congr _ fun ck => ?_
    rw [eval_unlinkOracleProgram_mkSig_issue Com nfGen tag S bound sys _ pk ctx 2 2 mkSig
      (by omega) (by omega) hmksig (fun _ => rfl) (fun _ _ _ _ _ => rfl) guardBoth b ck]
    have hstep (nf0 : Nullifier) (r0 : O) (nf1 : Nullifier) (r1 : O) :
        ProbComp.eval ((preLoopOracle Com nfGen tag S bound
          (balancePartitionRefundAdversary tag pk ctx mkSig) ck pk ctx guardBoth b 2 (by omega)
          ⟨nf0, 2, r0, Com.eval ck ⟨nf0, ctx, 2⟩ r0, 0,
            mkSig (tag (Com.eval ck ⟨nf0, ctx, 2⟩ r0) 0)⟩
          ⟨nf1, 2, r1, Com.eval ck ⟨nf1, ctx, 2⟩ r1, 0,
            mkSig (tag (Com.eval ck ⟨nf1, ctx, 2⟩ r1) 0)⟩ ()).run
          (realProofOracle Com tag S bound sys ck)) = PMF.pure res := by
      rw [eval_refund_preLoopOracle Com nfGen tag S bound sys hbound pk ctx mkSig hmksig ck
        guardBoth b nf0 nf1 r0 r1]
      simp only [hchal ck, PMF.bind_const]
    simp only [hstep, PMF.bind_const]
  · simp only [PMF.bind_const]

/-- Even when `T₀ = T₁`, omitting the cross-branch non-abort guard lets
`balancePartitionRefundAdversary` achieve advantage `1` whenever `bound ≥ 5`. -/
theorem balancePartitionRefund_unguarded_advantage_eq_one
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (hbound : 5 ≤ bound) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true) :
    Game.advantage
      (unguardedUnlinkabilityExperiment Com nfGen tag S bound sys
        (balancePartitionRefundAdversary tag pk ctx mkSig) false)
      (unguardedUnlinkabilityExperiment Com nfGen tag S bound sys
        (balancePartitionRefundAdversary tag pk ctx mkSig) true) = 1 := by
  let adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig Unit 2 1 :=
    balancePartitionRefundAdversary tag pk ctx mkSig
  have hside (b : Bool) :
      unguardedUnlinkabilityExperiment Com nfGen tag S bound sys adv b = PMF.pure (!b) :=
    eval_balancePartitionRefund_eq Com nfGen tag S bound sys hbound pk ctx mkSig hmksig
      false b (!b) fun ck nf0' r0' nf1' r1' => by
      cases b
      · simp only [preLoopOracle, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
        rw [eval_challengeLoop_debit2_true Com nfGen tag S bound sys adv (by omega) pk ctx
          mkSig hmksig (fun _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ => rfl) ck false _
          1 0 ⟨by simp, by simp; omega⟩ (by simp) rfl (by simp; omega) (by simp; omega)
          (by simp [hmksig])]
        simp only [PMF.bind_const]
      · simp only [preLoopOracle, ↓reduceIte, Bool.not_true]
        exact eval_challengeLoop_debit2_false Com nfGen tag S bound sys adv (fun _ => rfl) ck
          pk ctx false _ 1 2 (Or.inl (by simp))
  rw [hside false, hside true]
  exact NNReal.eq_iff.mpr (by simp [Game.coe_succProbability])

/-- With the cross-branch non-abort guard enabled, `balancePartitionRefundAdversary` also aborts
identically in both worlds and achieves unlinkability advantage `0`. -/
theorem balancePartitionRefund_guarded_advantage_eq_zero
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (hbound : 5 ≤ bound) (pk : PK) (ctx : Context) (mkSig : Target → Sig)
    (hmksig : ∀ t, S.verify pk t (mkSig t) = true) :
    Game.advantage
      (unlinkabilityExperiment Com nfGen tag S bound sys
        (balancePartitionRefundAdversary tag pk ctx mkSig) false)
      (unlinkabilityExperiment Com nfGen tag S bound sys
        (balancePartitionRefundAdversary tag pk ctx mkSig) true) = 0 := by
  let adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig Unit 2 1 :=
    balancePartitionRefundAdversary tag pk ctx mkSig
  have hzero (b : Bool) : unlinkabilityExperiment Com nfGen tag S bound sys adv b =
      PMF.pure false :=
    eval_balancePartitionRefund_eq Com nfGen tag S bound sys hbound pk ctx mkSig hmksig
      true b false fun ck nf0' r0' nf1' r1' => by
      cases b
      · exact eval_challengeLoop_debit2_false Com nfGen tag S bound sys adv (fun _ => rfl) ck pk
          ctx true _ 1 0 (Or.inr ⟨rfl, by simp⟩)
      · exact eval_challengeLoop_debit2_false Com nfGen tag S bound sys adv (fun _ => rfl) ck pk
          ctx true _ 1 2 (Or.inl (by simp))
  rw [hzero false, hzero true, Game.advantage_self]

end BalancePartitionAttacks

end UnlinkabilityGame

section UnlinkabilityReduction

variable {CommitKey PK C Context Nullifier O Sig Target SK Proof State : Type}

/-- Loop invariant guaranteeing that every client note holds a valid signature under `pk` and a
commitment opening within `bound`. -/
private def NoteInv
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig)
    (bound : ℕ) (ck : CommitKey) (pk : PK) (ctx : Context)
    (note : ClientNote Nullifier C O Sig) : Prop :=
  note.com = Com.eval ck ⟨note.nf, ctx, note.bal⟩ note.r ∧
    note.bal < bound ∧ note.ref < bound ∧
    S.verify pk (tag note.com note.ref) note.sig = true

section SimHybrid

/-- Explicit multi-instance ZK distinguisher for the adaptive unlinkability reduction (concrete
query-bounded step, `#7068`): draws a uniform challenge bit `b ← Bool`, runs `unlinkOracleProgram`
on `b`, and tests whether the adversary's output equals `b` (giving the factor of `2` via
`Game.advantage_le_two_mul_uniform_bool_xor`). -/
noncomputable def zkDistinguisher
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends) (ck : CommitKey) :
    ProbOracleComp (ProofSpec PK C Context Nullifier O Sig Proof) Bool := do
  let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let g ← unlinkOracleProgram Com nfGen tag S bound adv true b ck
  return decide (g = b)

/-- Query bound for `challengeLoopOracle`: at most `rem` queries. -/
private lemma challengeLoopOracle_isQueryBounded
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (ck : CommitKey) (pk : PK) (ctx : Context) (guardBoth : Bool)
    (rem : ℕ) (hrem : rem ≤ challengeSpends)
    (noteAct : ClientNote Nullifier C O Sig) (balOther refOther : ℕ) (st : State) :
    ProbOracleComp.IsQueryBounded
      (challengeLoopOracle Com nfGen tag S bound adv ck pk ctx guardBoth rem hrem
        noteAct balOther refOther st)
      rem := by
  induction rem generalizing noteAct balOther refOther st with
  | zero =>
    simp only [challengeLoopOracle]
    exact ProbOracleComp.IsQueryBounded.sample _
  | succ rem' ih =>
    simp only [challengeLoopOracle]
    conv_rhs => rw [← Nat.zero_add (rem' + 1)]
    refine (ProbOracleComp.IsQueryBounded.sample _).bind fun _ => ?_
    split_ifs
    · exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)
    · conv_rhs => rw [← Nat.zero_add (rem' + 1)]
      refine (ProbOracleComp.IsQueryBounded.sample _).bind fun _ => ?_
      conv_rhs => rw [← Nat.zero_add (rem' + 1)]
      refine (ProbOracleComp.IsQueryBounded.sample _).bind fun _ => ?_
      conv_rhs => rw [show rem' + 1 = 1 + rem' by omega]
      refine (ProbOracleComp.IsQueryBounded.query _).bind fun pi? => ?_
      cases pi? with
      | none => exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)
      | some pi =>
        conv_rhs => rw [← Nat.zero_add rem']
        refine (ProbOracleComp.IsQueryBounded.sample _).bind fun resp => ?_
        split_ifs
        · exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)
        · exact ih (by omega) _ _ _ _

/-- Query bound for `preLoopOracle`: at most `rem + challengeSpends` queries. -/
private lemma preLoopOracle_isQueryBounded
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (ck : CommitKey) (pk : PK) (ctx : Context) (guardBoth b : Bool)
    (rem : ℕ) (hrem : rem ≤ preRounds)
    (note0 note1 : ClientNote Nullifier C O Sig) (st : State) :
    ProbOracleComp.IsQueryBounded
      (preLoopOracle Com nfGen tag S bound adv ck pk ctx guardBoth b rem hrem note0 note1 st)
      (rem + challengeSpends) := by
  induction rem generalizing note0 note1 st with
  | zero =>
    simp only [preLoopOracle, Nat.zero_add]
    split_ifs <;>
      exact challengeLoopOracle_isQueryBounded Com nfGen tag S bound adv ck pk ctx guardBoth
        challengeSpends (le_refl _) _ _ _ _
  | succ rem' ih =>
    simp only [preLoopOracle]
    conv_rhs => rw [← Nat.zero_add (rem' + 1 + challengeSpends)]
    refine (ProbOracleComp.IsQueryBounded.sample _).bind fun _ => ?_
    split_ifs <;> first
      | exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)
      | (conv_rhs => rw [← Nat.zero_add (rem' + 1 + challengeSpends)]
         refine (ProbOracleComp.IsQueryBounded.sample _).bind fun _ => ?_
         conv_rhs => rw [← Nat.zero_add (rem' + 1 + challengeSpends)]
         refine (ProbOracleComp.IsQueryBounded.sample _).bind fun _ => ?_
         conv_rhs =>
           rw [show rem' + 1 + challengeSpends = 1 + (rem' + challengeSpends) by omega]
         refine (ProbOracleComp.IsQueryBounded.query _).bind fun pi? => ?_
         cases pi? with
         | none => exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)
         | some pi =>
           conv_rhs => rw [← Nat.zero_add (rem' + challengeSpends)]
           refine (ProbOracleComp.IsQueryBounded.sample _).bind fun _ => ?_
           split_ifs <;> first
             | exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)
             | exact ih (by omega) _ _ _)

private lemma issueStep_isQueryBounded
    (nfGen : ProbComp Nullifier) (sampleOpen : ProbComp O)
    (q : Nullifier → O → ProofQuery PK C Context Nullifier O Sig) {n : ℕ}
    (k : Nullifier → O → Option Proof →
      ProbOracleComp (ProofSpec PK C Context Nullifier O Sig Proof) Bool)
    (hkNone : ∀ nf r, (k nf r none).IsQueryBounded n)
    (hkSome : ∀ nf r pi, (k nf r (some pi)).IsQueryBounded n) :
    ((do
      let nf ← ProbOracleComp.sample nfGen
      let r ← ProbOracleComp.sample sampleOpen
      let pi? ← ProbOracleComp.query (q nf r)
      k nf r pi? :
        ProbOracleComp (ProofSpec PK C Context Nullifier O Sig Proof) Bool)).IsQueryBounded
      (1 + n) := by
  conv_rhs => rw [← Nat.zero_add (1 + n)]
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun nf => ?_
  conv_rhs => rw [← Nat.zero_add (1 + n)]
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun r => ?_
  refine (ProbOracleComp.IsQueryBounded.query _).bind fun pi? => ?_
  cases pi? with
  | none => exact hkNone nf r
  | some pi => exact hkSome nf r pi

/-- `zkDistinguisher` makes at most `2 + preRounds + challengeSpends` calls to `ProofOracle`. -/
theorem zkDistinguisher_isQueryBounded
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier) (tag : C → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    {preRounds challengeSpends : ℕ}
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends) (ck : CommitKey) :
    ProbOracleComp.IsQueryBounded (zkDistinguisher Com nfGen tag S bound adv ck)
      (2 + preRounds + challengeSpends) := by
  simp only [zkDistinguisher]
  conv_rhs => rw [← Nat.zero_add (2 + preRounds + challengeSpends)]
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun _ => ?_
  refine (?_ : ProbOracleComp.IsQueryBounded _ (2 + preRounds + challengeSpends)).bind
    (fun _ => OracleComp.IsCostBounded.pure _ 0)
  simp only [unlinkOracleProgram]
  conv_rhs => rw [← Nat.zero_add (2 + preRounds + challengeSpends)]
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun initOut => ?_
  split_ifs
  · exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)
  · rw [show 2 + preRounds + challengeSpends = 1 + (1 + (preRounds + challengeSpends)) by omega]
    refine issueStep_isQueryBounded nfGen Com.openSample _ _
      (fun _ _ => (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)) fun _ _ _ => ?_
    refine issueStep_isQueryBounded nfGen Com.openSample _ _
      (fun _ _ => (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)) fun _ _ _ => ?_
    conv_rhs => rw [← Nat.zero_add (preRounds + challengeSpends)]
    refine (ProbOracleComp.IsQueryBounded.sample _).bind fun _ => ?_
    split_ifs
    · exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)
    · exact preLoopOracle_isQueryBounded Com nfGen tag S bound adv ck _ _ true _
        _ (le_refl _) _ _ _

end SimHybrid

end UnlinkabilityReduction

section UnlinkabilityReductionContinuation

variable {CommitKey PK C Context Nullifier O Sig Target SK Proof State : Type}

/-- Environment bundling fixed protocol parameters across simulator hybrid loops. -/
private structure SimEnv
    (CommitKey PK C Context Nullifier O Sig Target SK Proof : Type) where
  /-- Deterministic-evaluation opening commitment scheme. -/
  Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O
  /-- Fresh nullifier sampler. -/
  nfGen : ProbComp Nullifier
  /-- Commitment-refund tag function. -/
  tag : C → ℕ → Target
  /-- Blind/issuer signature scheme. -/
  S : Signature.Scheme PK SK Target Sig
  /-- Protocol integer range bound. -/
  bound : ℕ
  /-- Prover and zero-knowledge simulator system. -/
  sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof
  /-- Sampled public commitment key. -/
  ck : CommitKey
  /-- Fixed dummy nullifier used in dummy-message commitment slots. -/
  dummyNf : Nullifier

/-- Challenge-spend simulator loop parameterized by commitment hybrid cutoff `hop` (`idx < hop`
uses `dummy`, `hop ≤ idx` uses the real note message). -/
private def challengeLoopSim {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (hop : ℕ)
    (rem : ℕ) (hrem : rem ≤ challengeSpends)
    (noteAct : SimNote Nullifier) (balOther refOther : ℕ) (st : State) : ProbComp Bool :=
  match rem with
  | 0 => adv.guess st
  | rem' + 1 =>
    let j : Fin challengeSpends := ⟨challengeSpends - (rem' + 1), by omega⟩
    let idx := 2 + preRounds + (challengeSpends - (rem' + 1))
    do
      let choice ← adv.chooseChallenge j st
      let okAct := spendAdmissible env.bound noteAct.bal noteAct.ref choice.debit
      let okOther := spendAdmissible env.bound balOther refOther choice.debit
      if !(okAct && okOther) then
        return false
      else
        let nfPrime ← env.nfGen
        let rPrime ← env.Com.openSample
        let tPrime := noteAct.bal + noteAct.ref - choice.debit
        let realMsg : CommitMsg Nullifier Context := ⟨nfPrime, ctx, tPrime⟩
        let dummyMsg : CommitMsg Nullifier Context := ⟨env.dummyNf, ctx, 0⟩
        let cPrime := env.Com.eval env.ck (if idx < hop then dummyMsg else realMsg) rPrime
        let pi ← env.sys.simulate env.ck (.spend ⟨pk, ctx, noteAct.nf, choice.debit, cPrime⟩)
        let resp ← adv.finalizeChallenge j choice.st noteAct.nf choice.debit cPrime pi
        if !(resp.refund < env.bound &&
            env.S.verify pk (env.tag cPrime resp.refund) resp.sig) then
          return false
        else
          let noteNext : SimNote Nullifier := ⟨nfPrime, tPrime, resp.refund⟩
          let balOtherNext := balOther + refOther - choice.debit
          challengeLoopSim env adv pk ctx hop rem' (by omega)
            noteNext balOtherNext resp.refund resp.st

/-- Pre-challenge simulator loop parameterized by commitment hybrid cutoff `hop`. -/
private def preLoopSim {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (b : Bool) (hop : ℕ)
    (rem : ℕ) (hrem : rem ≤ preRounds)
    (note0 note1 : SimNote Nullifier) (st : State) : ProbComp Bool :=
  match rem with
  | 0 =>
    if b then
      challengeLoopSim env adv pk ctx hop challengeSpends (le_refl _)
        note1 note0.bal note0.ref st
    else
      challengeLoopSim env adv pk ctx hop challengeSpends (le_refl _)
        note0 note1.bal note1.ref st
  | rem' + 1 =>
    let i : Fin preRounds := ⟨preRounds - (rem' + 1), by omega⟩
    let idx := 2 + (preRounds - (rem' + 1))
    do
      let choice ← adv.choosePre i st
      let noteSel := if choice.client then note1 else note0
      if !spendAdmissible env.bound noteSel.bal noteSel.ref choice.debit then
        return false
      else
        let nfPrime ← env.nfGen
        let rPrime ← env.Com.openSample
        let tPrime := noteSel.bal + noteSel.ref - choice.debit
        let realMsg : CommitMsg Nullifier Context := ⟨nfPrime, ctx, tPrime⟩
        let dummyMsg : CommitMsg Nullifier Context := ⟨env.dummyNf, ctx, 0⟩
        let cPrime := env.Com.eval env.ck (if idx < hop then dummyMsg else realMsg) rPrime
        let pi ← env.sys.simulate env.ck (.spend ⟨pk, ctx, noteSel.nf, choice.debit, cPrime⟩)
        let resp ← adv.finalizePre i choice.st noteSel.nf choice.debit cPrime pi
        if !(resp.refund < env.bound &&
            env.S.verify pk (env.tag cPrime resp.refund) resp.sig) then
          return false
        else
          let noteUpdated : SimNote Nullifier := ⟨nfPrime, tPrime, resp.refund⟩
          let note0' := if choice.client then note0 else noteUpdated
          let note1' := if choice.client then noteUpdated else note1
          preLoopSim env adv pk ctx b hop rem' (by omega) note0' note1' resp.st

/-- Full direct-simulator hybrid game at cutoff `hop : ℕ` (`0` = `G1`, `2 + pre + chal` = `G4`). -/
private def runSimProgram {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (b : Bool) (hop : ℕ) : ProbComp Bool := do
  let initOut ← adv.init env.ck
  if !(0 < initOut.t0 && initOut.t0 < env.bound &&
      0 < initOut.t1 && initOut.t1 < env.bound) then
    return false
  else
    let dummyMsg : CommitMsg Nullifier Context := ⟨env.dummyNf, initOut.ctx, 0⟩
    let nf0 ← env.nfGen
    let r0 ← env.Com.openSample
    let c0 := env.Com.eval env.ck
      (if 0 < hop then dummyMsg else ⟨nf0, initOut.ctx, initOut.t0⟩) r0
    let pi0 ← env.sys.simulate env.ck (.issue ⟨initOut.ctx, c0, initOut.t0⟩)
    let nf1 ← env.nfGen
    let r1 ← env.Com.openSample
    let c1 := env.Com.eval env.ck
      (if 1 < hop then dummyMsg else ⟨nf1, initOut.ctx, initOut.t1⟩) r1
    let pi1 ← env.sys.simulate env.ck (.issue ⟨initOut.ctx, c1, initOut.t1⟩)
    let issResp ← adv.issue initOut.st c0 pi0 c1 pi1
    if !(env.S.verify initOut.pk (env.tag c0 0) issResp.s0 &&
        env.S.verify initOut.pk (env.tag c1 0) issResp.s1) then
      return false
    else
      let note0 : SimNote Nullifier := ⟨nf0, initOut.t0, 0⟩
      let note1 : SimNote Nullifier := ⟨nf1, initOut.t1, 0⟩
      preLoopSim env adv initOut.pk initOut.ctx b hop preRounds (le_refl _)
        note0 note1 issResp.st

/-- Cutoff congruence for `challengeLoopSim` once `hop₁, hop₂ ≤ idx0`. -/
private lemma challengeLoopSim_cutoff_congr {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (hop1 hop2 : ℕ)
    (rem : ℕ) (hrem : rem ≤ challengeSpends)
    (h1 : hop1 ≤ 2 + preRounds + (challengeSpends - rem))
    (h2 : hop2 ≤ 2 + preRounds + (challengeSpends - rem))
    (noteAct : SimNote Nullifier) (balOther refOther : ℕ) (st : State) :
    challengeLoopSim env adv pk ctx hop1 rem hrem noteAct balOther refOther st =
      challengeLoopSim env adv pk ctx hop2 rem hrem noteAct balOther refOther st := by
  induction rem generalizing noteAct balOther refOther st with
  | zero => rfl
  | succ rem' ih =>
    have hf1 : ¬ (2 + preRounds + (challengeSpends - (rem' + 1)) < hop1) := by omega
    have hf2 : ¬ (2 + preRounds + (challengeSpends - (rem' + 1)) < hop2) := by omega
    simp only [challengeLoopSim, hf1, hf2, ↓reduceIte]
    congr 1 with choice
    split_ifs
    · rfl
    · congr 1 with nfPrime
      congr 1 with rPrime
      congr 1 with pi
      congr 1 with resp
      split_ifs
      · rfl
      · exact ih (by omega) (by omega) (by omega) _ _ _ _

/-- Cutoff congruence for `preLoopSim` once `hop₁, hop₂ ≤ idx0`. -/
private lemma preLoopSim_cutoff_congr {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (b : Bool) (hop1 hop2 : ℕ)
    (rem : ℕ) (hrem : rem ≤ preRounds)
    (h1 : hop1 ≤ 2 + (preRounds - rem)) (h2 : hop2 ≤ 2 + (preRounds - rem))
    (note0 note1 : SimNote Nullifier) (st : State) :
    preLoopSim env adv pk ctx b hop1 rem hrem note0 note1 st =
      preLoopSim env adv pk ctx b hop2 rem hrem note0 note1 st := by
  induction rem generalizing note0 note1 st with
  | zero =>
    cases b <;>
      exact challengeLoopSim_cutoff_congr env adv pk ctx hop1 hop2 challengeSpends
        (le_refl _) (by omega) (by omega) _ _ _ _
  | succ rem' ih =>
    have hf1 : ¬ (2 + (preRounds - (rem' + 1)) < hop1) := by omega
    have hf2 : ¬ (2 + (preRounds - (rem' + 1)) < hop2) := by omega
    simp only [preLoopSim, hf1, hf2, ↓reduceIte]
    congr 1 with choice
    cases hguard : spendAdmissible env.bound
        (if choice.client then note1 else note0).bal
        (if choice.client then note1 else note0).ref choice.debit
    · simp only [Bool.not_false, ↓reduceIte]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      congr 1 with nfPrime
      congr 1 with rPrime
      congr 1 with pi
      congr 1 with resp
      split_ifs <;> first | rfl | exact ih (by omega) (by omega) (by omega) _ _ _

/-- Shared helper collapsing a valid `simProofOracle` query bind into `sys.simulate` at `PMF`
level. -/
private lemma bind_simProofOracle_valid [DecidableEq C]
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    {stmt : ProofStatement PK C Context Nullifier} {wit : ProofWitness O Sig Nullifier}
    (ck : CommitKey)
    (hval : validStatement Com tag S bound ck stmt wit = true)
    (k : Option Proof → PMF Bool) :
    (ProbComp.eval (simProofOracle Com tag S bound sys ck ⟨stmt, wit⟩)).bind k =
    (ProbComp.eval (sys.simulate ck stmt)).bind fun pi => k (some pi) := by
  simp only [simProofOracle, hval, ↓reduceIte, ProbComp.eval_map, PMF.bind_map, Function.comp_def]

private lemma spendValid_of_noteInv [DecidableEq C]
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (pk : PK) (ctx : Context) (note : ClientNote Nullifier C O Sig) (debit : ℕ)
    (nfPrime : Nullifier) (rPrime : O)
    (hinv : NoteInv env.Com env.tag env.S env.bound env.ck pk ctx note)
    (hok : spendAdmissible env.bound note.bal note.ref debit = true) :
    validStatement env.Com env.tag env.S env.bound env.ck
      (.spend ⟨pk, ctx, note.nf, debit,
        env.Com.eval env.ck ⟨nfPrime, ctx, note.bal + note.ref - debit⟩ rPrime⟩)
      (.spend ⟨note.bal, note.r, note.ref, note.sig, nfPrime,
        note.bal + note.ref - debit, rPrime⟩) = true := by
  rcases hinv with ⟨hcom, hbal, href, hsig⟩
  simp only [spendAdmissible, decide_eq_true_eq] at hok
  simp only [validStatement, ← hcom, hsig, Bool.true_and, decide_eq_true_eq]
  exact ⟨by simp, hok.2.1, by simp, hbal, href, hok.2.2, hok.1⟩

private lemma eval_simGate [DecidableEq C]
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof) (ck : CommitKey)
    (c1 c2 : Bool)
    (kOra : ProbOracleComp (ProofSpec PK C Context Nullifier O Sig Proof) Bool)
    (kSim : ProbComp Bool)
    (hk : c1 = true → c2 = true →
      ProbComp.eval (kOra.run (simProofOracle Com tag S bound sys ck)) = ProbComp.eval kSim) :
    ProbComp.eval ((if !(c1 && c2) then pure false else kOra).run
        (simProofOracle Com tag S bound sys ck)) =
      ProbComp.eval (if !(c1 && c2) then pure false else kSim) := by
  cases hfin : c1 && c2
  · simp only [Bool.not_false, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hc := (Bool.and_eq_true _ _).mp hfin
    exact hk hc.1 hc.2

private lemma issueValid_of_pos_lt [DecidableEq C]
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (ck : CommitKey) (ctx : Context) (t : ℕ) (nf : Nullifier) (r : O)
    (htpos : 0 < t) (htub : t < bound) :
    validStatement Com tag S bound ck
      (.issue ⟨ctx, Com.eval ck ⟨nf, ctx, t⟩ r, t⟩) (.issue ⟨nf, r⟩) = true := by
  simp [validStatement, htpos, htub]

/-- Equivalence between `challengeLoopOracle` under `simProofOracle` and `challengeLoopSim` at
`hop = 0` whenever the active note satisfies `NoteInv`. -/
private lemma challengeLoopOracle_sim_eq [DecidableEq C] {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (rem : ℕ) (hrem : rem ≤ challengeSpends)
    (noteAct : ClientNote Nullifier C O Sig) (balOther refOther : ℕ) (st : State)
    (hinv : NoteInv env.Com env.tag env.S env.bound env.ck pk ctx noteAct) :
    ProbComp.eval ((challengeLoopOracle env.Com env.nfGen env.tag env.S env.bound adv env.ck pk
        ctx true rem hrem noteAct balOther refOther st).run
        (simProofOracle env.Com env.tag env.S env.bound env.sys env.ck)) =
      ProbComp.eval (challengeLoopSim env adv pk ctx 0 rem hrem noteAct.toSim balOther
        refOther st) := by
  induction rem generalizing noteAct balOther refOther st with
  | zero =>
    simp [challengeLoopOracle, challengeLoopSim, ProbOracleComp.run_sample]
  | succ rem' ih =>
    have htrueOr : ∀ x : Bool, (!true || x) = x := fun x => by cases x <;> rfl
    simp only [challengeLoopOracle, challengeLoopSim, ClientNote.toSim, Nat.not_lt_zero, htrueOr,
      ↓reduceIte, ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbComp.eval_bind]
    refine pmfBind_congr _ fun choice => ?_
    cases hguard : spendAdmissible env.bound noteAct.bal noteAct.ref choice.debit &&
        spendAdmissible env.bound balOther refOther choice.debit
    · simp only [Bool.not_false, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_bind,
        ProbOracleComp.run_sample, ProbOracleComp.run_query, ProbComp.eval_bind]
      have hokAct : spendAdmissible env.bound noteAct.bal noteAct.ref choice.debit = true :=
        ((Bool.and_eq_true _ _).mp hguard).1
      have hokAct' := by simpa only [spendAdmissible, decide_eq_true_eq] using hokAct
      refine pmfBind_congr _ fun nfPrime => pmfBind_congr _ fun rPrime => ?_
      rw [bind_simProofOracle_valid env.Com env.tag env.S env.bound env.sys env.ck
        (spendValid_of_noteInv env pk ctx noteAct choice.debit nfPrime rPrime hinv hokAct)]
      dsimp only
      refine pmfBind_congr _ fun pi => ?_
      simp only [ProbOracleComp.run_sample, ProbOracleComp.run_bind, ProbComp.eval_bind]
      refine pmfBind_congr _ fun resp => eval_simGate env.Com env.tag env.S env.bound env.sys
        env.ck (decide (resp.refund < env.bound)) _ _ _ fun hrf hvs => ?_
      rw [decide_eq_true_eq] at hrf
      simpa only [ClientNote.toSim] using ih (by omega) _ _ _ _ ⟨rfl, hokAct'.2.2, hrf, hvs⟩

/-- Equivalence between `preLoopOracle` under `simProofOracle` and `preLoopSim` at `hop = 0`
whenever both client notes satisfy `NoteInv`. -/
private lemma preLoopOracle_sim_eq [DecidableEq C] {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (b : Bool) (rem : ℕ) (hrem : rem ≤ preRounds)
    (note0 note1 : ClientNote Nullifier C O Sig) (st : State)
    (h0 : NoteInv env.Com env.tag env.S env.bound env.ck pk ctx note0)
    (h1 : NoteInv env.Com env.tag env.S env.bound env.ck pk ctx note1) :
    ProbComp.eval ((preLoopOracle env.Com env.nfGen env.tag env.S env.bound adv env.ck pk ctx
        true b rem hrem note0 note1 st).run
        (simProofOracle env.Com env.tag env.S env.bound env.sys env.ck)) =
      ProbComp.eval (preLoopSim env adv pk ctx b 0 rem hrem note0.toSim note1.toSim st) := by
  induction rem generalizing note0 note1 st with
  | zero =>
    cases b
    · exact challengeLoopOracle_sim_eq env adv pk ctx challengeSpends (le_refl _)
        note0 note1.bal note1.ref st h0
    · exact challengeLoopOracle_sim_eq env adv pk ctx challengeSpends (le_refl _)
        note1 note0.bal note0.ref st h1
  | succ rem' ih =>
    simp only [preLoopOracle, preLoopSim, Nat.not_lt_zero, ↓reduceIte, ProbOracleComp.run_bind,
      ProbOracleComp.run_sample, ProbComp.eval_bind]
    refine pmfBind_congr _ fun choice => ?_
    set noteSel := if choice.client then note1 else note0
    have hsel : NoteInv env.Com env.tag env.S env.bound env.ck pk ctx noteSel := by
      cases hcl : choice.client <;> simp only [noteSel, hcl, ↓reduceIte, Bool.false_eq_true]
      · exact h0
      · exact h1
    have hsimSel : (if choice.client then note1.toSim else note0.toSim) = noteSel.toSim := by
      cases hcl : choice.client <;> simp [noteSel, hcl]
    rw [hsimSel]
    by_cases hguard : spendAdmissible env.bound noteSel.bal noteSel.ref choice.debit = false
    · simp only [hguard, Bool.not_false, ↓reduceIte, ClientNote.toSim, ProbOracleComp.run_pure,
        ProbComp.eval_pure]
    · have hokSel := Bool.eq_true_of_not_eq_false hguard
      simp only [hokSel, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ClientNote.toSim,
        ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_query,
        ProbComp.eval_bind]
      have hokSel' := by simpa only [spendAdmissible, decide_eq_true_eq] using hokSel
      refine pmfBind_congr _ fun nfPrime => pmfBind_congr _ fun rPrime => ?_
      rw [bind_simProofOracle_valid env.Com env.tag env.S env.bound env.sys env.ck
        (spendValid_of_noteInv env pk ctx noteSel choice.debit nfPrime rPrime hsel hokSel)]
      dsimp only
      refine pmfBind_congr _ fun pi => ?_
      simp only [ProbOracleComp.run_sample, ProbOracleComp.run_bind, ProbComp.eval_bind]
      refine pmfBind_congr _ fun resp => eval_simGate env.Com env.tag env.S env.bound env.sys
        env.ck (decide (resp.refund < env.bound)) _ _ _ fun hrf hvs => ?_
      rw [decide_eq_true_eq] at hrf
      cases choice.client
      · simp only [↓reduceIte, Bool.false_eq_true, noteSel] at hsel ⊢
        simpa only [ClientNote.toSim] using ih (by omega) _ _ _ ⟨rfl, hokSel'.2.2, hrf, hvs⟩ h1
      · simp only [↓reduceIte, noteSel] at hsel ⊢
        simpa only [ClientNote.toSim] using ih (by omega) _ _ _ h0 ⟨rfl, hokSel'.2.2, hrf, hvs⟩

/-- Equivalence between `unlinkOracleProgram` under `simProofOracle` and `runSimProgram` at
`hop = 0`. -/
private lemma unlinkOracleProgram_sim_eq [DecidableEq C] {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends) (b : Bool) :
    ProbComp.eval ((unlinkOracleProgram env.Com env.nfGen env.tag env.S env.bound adv true b
        env.ck).run (simProofOracle env.Com env.tag env.S env.bound env.sys env.ck)) =
      ProbComp.eval (runSimProgram env adv b 0) := by
  simp only [unlinkOracleProgram, runSimProgram, Nat.not_lt_zero, ↓reduceIte,
    ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbComp.eval_bind]
  refine pmfBind_congr _ fun initOut => ?_
  cases hinit : decide (0 < initOut.t0) && decide (initOut.t0 < env.bound) &&
      decide (0 < initOut.t1) && decide (initOut.t1 < env.bound)
  · simp only [Bool.not_false, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_bind,
      ProbOracleComp.run_sample, ProbOracleComp.run_query, ProbComp.eval_bind]
    obtain ⟨ht0pos, ht0ub, ht1pos, ht1ub⟩ := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hinit
    refine pmfBind_congr _ fun nf0 => pmfBind_congr _ fun r0 => ?_
    rw [bind_simProofOracle_valid env.Com env.tag env.S env.bound env.sys env.ck
      (issueValid_of_pos_lt env.Com env.tag env.S env.bound env.ck initOut.ctx initOut.t0
        nf0 r0 ht0pos ht0ub)]
    dsimp only
    refine pmfBind_congr _ fun pi0 => ?_
    simp only [ProbOracleComp.run_sample, ProbOracleComp.run_bind, ProbOracleComp.run_query,
      ProbComp.eval_bind]
    refine pmfBind_congr _ fun nf1 => pmfBind_congr _ fun r1 => ?_
    rw [bind_simProofOracle_valid env.Com env.tag env.S env.bound env.sys env.ck
      (issueValid_of_pos_lt env.Com env.tag env.S env.bound env.ck initOut.ctx initOut.t1
        nf1 r1 ht1pos ht1ub)]
    dsimp only
    refine pmfBind_congr _ fun pi1 => ?_
    simp only [ProbOracleComp.run_sample, ProbOracleComp.run_bind, ProbComp.eval_bind]
    refine pmfBind_congr _ fun issResp => ?_
    cases hiss : env.S.verify initOut.pk (env.tag
        (env.Com.eval env.ck ⟨nf0, initOut.ctx, initOut.t0⟩ r0) 0) issResp.s0 &&
        env.S.verify initOut.pk (env.tag
        (env.Com.eval env.ck ⟨nf1, initOut.ctx, initOut.t1⟩ r1) 0) issResp.s1
    · simp only [Bool.not_false, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hsigs := (Bool.and_eq_true _ _).mp hiss
      exact preLoopOracle_sim_eq env adv initOut.pk initOut.ctx b preRounds (le_refl _)
        ⟨nf0, initOut.t0, r0, env.Com.eval env.ck ⟨nf0, initOut.ctx, initOut.t0⟩ r0, 0, issResp.s0⟩
        ⟨nf1, initOut.t1, r1, env.Com.eval env.ck ⟨nf1, initOut.ctx, initOut.t1⟩ r1, 0, issResp.s1⟩
        issResp.st
        ⟨rfl, ht0ub, show (0 : ℕ) < env.bound by omega, hsigs.1⟩
        ⟨rfl, ht1ub, show (0 : ℕ) < env.bound by omega, hsigs.2⟩

/-- Challenge pause step: stops right before commitment slot `idx` equals `pauseSlot`. -/
private def challengeLoopPause {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (pauseSlot : ℕ)
    (rem : ℕ) (hrem : rem ≤ challengeSpends)
    (noteAct : SimNote Nullifier) (balOther refOther : ℕ) (st : State) :
    ProbComp (PauseResult PK Context C Nullifier Proof State preRounds challengeSpends) :=
  match rem with
  | 0 => do
    let g ← adv.guess st
    return ⟨⟨env.dummyNf, ctx, 0⟩, ⟨env.dummyNf, ctx, 0⟩, .done g⟩
  | rem' + 1 =>
    let j : Fin challengeSpends := ⟨challengeSpends - (rem' + 1), by omega⟩
    let idx := 2 + preRounds + (challengeSpends - (rem' + 1))
    do
      let choice ← adv.chooseChallenge j st
      let okAct := spendAdmissible env.bound noteAct.bal noteAct.ref choice.debit
      let okOther := spendAdmissible env.bound balOther refOther choice.debit
      if !(okAct && okOther) then
        return ⟨⟨env.dummyNf, ctx, 0⟩, ⟨env.dummyNf, ctx, 0⟩, .done false⟩
      else
        let nfPrime ← env.nfGen
        let tPrime := noteAct.bal + noteAct.ref - choice.debit
        let realMsg : CommitMsg Nullifier Context := ⟨nfPrime, ctx, tPrime⟩
        let dummyMsg : CommitMsg Nullifier Context := ⟨env.dummyNf, ctx, 0⟩
        if idx = pauseSlot then
          return ⟨realMsg, dummyMsg,
            .chal pk ctx noteAct balOther refOther choice.st choice.debit nfPrime tPrime
              j.val j.isLt⟩
        else
          let rPrime ← env.Com.openSample
          let cPrime := env.Com.eval env.ck
            (if idx < pauseSlot then dummyMsg else realMsg) rPrime
          let pi ← env.sys.simulate env.ck (.spend ⟨pk, ctx, noteAct.nf, choice.debit, cPrime⟩)
          let resp ← adv.finalizeChallenge j choice.st noteAct.nf choice.debit cPrime pi
          if !(resp.refund < env.bound &&
              env.S.verify pk (env.tag cPrime resp.refund) resp.sig) then
            return ⟨dummyMsg, dummyMsg, .done false⟩
          else
            let noteNext : SimNote Nullifier := ⟨nfPrime, tPrime, resp.refund⟩
            challengeLoopPause env adv pk ctx pauseSlot rem' (by omega)
              noteNext (balOther + refOther - choice.debit) resp.refund resp.st

/-- Pre-challenge pause step: stops right before commitment slot `idx` equals `pauseSlot`. -/
private def preLoopPause {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (b : Bool) (pauseSlot : ℕ)
    (rem : ℕ) (hrem : rem ≤ preRounds)
    (note0 note1 : SimNote Nullifier) (st : State) :
    ProbComp (PauseResult PK Context C Nullifier Proof State preRounds challengeSpends) :=
  match rem with
  | 0 =>
    if b then
      challengeLoopPause env adv pk ctx pauseSlot challengeSpends (le_refl _)
        note1 note0.bal note0.ref st
    else
      challengeLoopPause env adv pk ctx pauseSlot challengeSpends (le_refl _)
        note0 note1.bal note1.ref st
  | rem' + 1 =>
    let i : Fin preRounds := ⟨preRounds - (rem' + 1), by omega⟩
    let idx := 2 + (preRounds - (rem' + 1))
    do
      let choice ← adv.choosePre i st
      let noteSel := if choice.client then note1 else note0
      if !spendAdmissible env.bound noteSel.bal noteSel.ref choice.debit then
        return ⟨⟨env.dummyNf, ctx, 0⟩, ⟨env.dummyNf, ctx, 0⟩, .done false⟩
      else
        let nfPrime ← env.nfGen
        let tPrime := noteSel.bal + noteSel.ref - choice.debit
        let realMsg : CommitMsg Nullifier Context := ⟨nfPrime, ctx, tPrime⟩
        let dummyMsg : CommitMsg Nullifier Context := ⟨env.dummyNf, ctx, 0⟩
        if idx = pauseSlot then
          return ⟨realMsg, dummyMsg,
            .pre b pk ctx note0 note1 choice.client choice.debit choice.st nfPrime tPrime
              i.val i.isLt⟩
        else
          let rPrime ← env.Com.openSample
          let cPrime := env.Com.eval env.ck
            (if idx < pauseSlot then dummyMsg else realMsg) rPrime
          let pi ← env.sys.simulate env.ck (.spend ⟨pk, ctx, noteSel.nf, choice.debit, cPrime⟩)
          let resp ← adv.finalizePre i choice.st noteSel.nf choice.debit cPrime pi
          if !(resp.refund < env.bound &&
              env.S.verify pk (env.tag cPrime resp.refund) resp.sig) then
            return ⟨dummyMsg, dummyMsg, .done false⟩
          else
            let noteUpdated : SimNote Nullifier := ⟨nfPrime, tPrime, resp.refund⟩
            let note0' := if choice.client then note0 else noteUpdated
            let note1' := if choice.client then noteUpdated else note1
            preLoopPause env adv pk ctx b pauseSlot rem' (by omega) note0' note1' resp.st

/-- Full hybrid prefix up to pause slot `pauseSlot`. -/
private def runPause {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (b : Bool) (pauseSlot : ℕ) :
    ProbComp (PauseResult PK Context C Nullifier Proof State preRounds challengeSpends) := do
  let initOut ← adv.init env.ck
  let dummyMsg : CommitMsg Nullifier Context := ⟨env.dummyNf, initOut.ctx, 0⟩
  if !(0 < initOut.t0 && initOut.t0 < env.bound &&
      0 < initOut.t1 && initOut.t1 < env.bound) then
    return ⟨dummyMsg, dummyMsg, .done false⟩
  else
    let nf0 ← env.nfGen
    if 0 = pauseSlot then
      return ⟨⟨nf0, initOut.ctx, initOut.t0⟩, dummyMsg,
        .issue0 b initOut.pk initOut.ctx initOut.t0 initOut.t1 initOut.st nf0⟩
    else
      let r0 ← env.Com.openSample
      let c0 := env.Com.eval env.ck dummyMsg r0
      let pi0 ← env.sys.simulate env.ck (.issue ⟨initOut.ctx, c0, initOut.t0⟩)
      let nf1 ← env.nfGen
      if 1 = pauseSlot then
        return ⟨⟨nf1, initOut.ctx, initOut.t1⟩, dummyMsg,
          .issue1 b initOut.pk initOut.ctx initOut.t0 initOut.t1 initOut.st nf0 c0 pi0 nf1⟩
      else
        let r1 ← env.Com.openSample
        let c1 := env.Com.eval env.ck dummyMsg r1
        let pi1 ← env.sys.simulate env.ck (.issue ⟨initOut.ctx, c1, initOut.t1⟩)
        let issResp ← adv.issue initOut.st c0 pi0 c1 pi1
        if !(env.S.verify initOut.pk (env.tag c0 0) issResp.s0 &&
            env.S.verify initOut.pk (env.tag c1 0) issResp.s1) then
          return ⟨dummyMsg, dummyMsg, .done false⟩
        else
          preLoopPause env adv initOut.pk initOut.ctx b pauseSlot preRounds (le_refl _)
            ⟨nf0, initOut.t0, 0⟩ ⟨nf1, initOut.t1, 0⟩ issResp.st

/-- Resume simulator hybrid after receiving challenge commitment `cStar` at slot `pauseSlot`. -/
private def resumeAfterCom {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pauseSlot : ℕ)
    (cont : SimContinuation PK Context C Nullifier Proof State preRounds challengeSpends)
    (cStar : C) : ProbComp Bool :=
  match cont with
  | .done res => pure res
  | .issue0 b pk ctx t0 t1 st nf0 => do
    let pi0 ← env.sys.simulate env.ck (.issue ⟨ctx, cStar, t0⟩)
    let nf1 ← env.nfGen
    let r1 ← env.Com.openSample
    let c1 := env.Com.eval env.ck ⟨nf1, ctx, t1⟩ r1
    let pi1 ← env.sys.simulate env.ck (.issue ⟨ctx, c1, t1⟩)
    let issResp ← adv.issue st cStar pi0 c1 pi1
    if !(env.S.verify pk (env.tag cStar 0) issResp.s0 &&
        env.S.verify pk (env.tag c1 0) issResp.s1) then
      return false
    else
      preLoopSim env adv pk ctx b (pauseSlot + 1) preRounds (le_refl _)
        ⟨nf0, t0, 0⟩ ⟨nf1, t1, 0⟩ issResp.st
  | .issue1 b pk ctx t0 t1 st nf0 c0 pi0 nf1 => do
    let pi1 ← env.sys.simulate env.ck (.issue ⟨ctx, cStar, t1⟩)
    let issResp ← adv.issue st c0 pi0 cStar pi1
    if !(env.S.verify pk (env.tag c0 0) issResp.s0 &&
        env.S.verify pk (env.tag cStar 0) issResp.s1) then
      return false
    else
      preLoopSim env adv pk ctx b (pauseSlot + 1) preRounds (le_refl _)
        ⟨nf0, t0, 0⟩ ⟨nf1, t1, 0⟩ issResp.st
  | .pre b pk ctx note0 note1 cClient d st nfPrime tPrime i hi => do
    let noteSel := if cClient then note1 else note0
    let pi ← env.sys.simulate env.ck (.spend ⟨pk, ctx, noteSel.nf, d, cStar⟩)
    let resp ← adv.finalizePre ⟨i, hi⟩ st noteSel.nf d cStar pi
    if !(resp.refund < env.bound && env.S.verify pk (env.tag cStar resp.refund) resp.sig) then
      return false
    else
      let noteUpdated : SimNote Nullifier := ⟨nfPrime, tPrime, resp.refund⟩
      let note0' := if cClient then note0 else noteUpdated
      let note1' := if cClient then noteUpdated else note1
      preLoopSim env adv pk ctx b (pauseSlot + 1) (preRounds - (i + 1)) (by omega)
        note0' note1' resp.st
  | .chal pk ctx noteAct balOther refOther st d nfPrime tPrime j hj => do
    let pi ← env.sys.simulate env.ck (.spend ⟨pk, ctx, noteAct.nf, d, cStar⟩)
    let resp ← adv.finalizeChallenge ⟨j, hj⟩ st noteAct.nf d cStar pi
    if !(resp.refund < env.bound && env.S.verify pk (env.tag cStar resp.refund) resp.sig) then
      return false
    else
      let noteNext : SimNote Nullifier := ⟨nfPrime, tPrime, resp.refund⟩
      challengeLoopSim env adv pk ctx (pauseSlot + 1) (challengeSpends - (j + 1)) (by omega)
        noteNext (balOther + refOther - d) resp.refund resp.st

/-- Pausing `challengeLoopPause` at `pauseSlot` and committing `msgReal` (`isDummy = false`) or
`msgDummy` (`isDummy = true`) reconstructs `challengeLoopSim` at cutoff `pauseSlot` or
`pauseSlot + 1`. -/
private lemma challengeLoopPause_resume_eq {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (isDummy : Bool) (pauseSlot rem : ℕ)
    (hrem : rem ≤ challengeSpends)
    (hslot : 2 + preRounds + (challengeSpends - rem) ≤ pauseSlot)
    (noteAct : SimNote Nullifier) (balOther refOther : ℕ) (st : State) :
    ProbComp.eval (do
        let res ← challengeLoopPause env adv pk ctx pauseSlot rem hrem noteAct balOther
          refOther st
        let r ← env.Com.openSample
        resumeAfterCom env adv pauseSlot res.cont
          (env.Com.eval env.ck (if isDummy then res.msgDummy else res.msgReal) r)) =
      ProbComp.eval (challengeLoopSim env adv pk ctx
        (if isDummy then pauseSlot + 1 else pauseSlot) rem hrem noteAct balOther refOther st) := by
  induction rem generalizing noteAct balOther refOther st with
  | zero =>
    simp [challengeLoopPause, challengeLoopSim, resumeAfterCom, ProbComp.eval_bind, PMF.map,
      Function.comp_def, PMF.bind_const, PMF.bind_pure]
  | succ rem' ih =>
    simp only [challengeLoopPause, challengeLoopSim, ProbComp.eval_bind, PMF.bind_bind]
    refine pmfBind_congr _ fun choice => ?_
    cases spendAdmissible env.bound noteAct.bal noteAct.ref choice.debit &&
        spendAdmissible env.bound balOther refOther choice.debit
    · simp only [Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
        PMF.pure_bind, PMF.bind_const]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind,
        PMF.bind_bind]
      refine pmfBind_congr _ fun nfPrime => ?_
      by_cases heq : 2 + preRounds + (challengeSpends - (rem' + 1)) = pauseSlot
      · have hrem_eq : challengeSpends - (challengeSpends - (rem' + 1) + 1) = rem' := by omega
        cases isDummy
        · simp only [heq, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.pure_bind, resumeAfterCom, hrem_eq, Nat.lt_irrefl]
          refine pmfBind_congr _ fun rPrime => pmfBind_congr _ fun pi =>
            pmfBind_congr _ fun resp => ?_
          split_ifs
          · rfl
          · exact congrArg ProbComp.eval (challengeLoopSim_cutoff_congr env adv pk ctx
              (pauseSlot + 1) pauseSlot rem' (by omega) (by omega) (by omega) _ _ _ _)
        · simp only [heq, ↓reduceIte, Nat.lt_succ_self, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.pure_bind, resumeAfterCom, hrem_eq]
      · have hlt : 2 + preRounds + (challengeSpends - (rem' + 1)) < pauseSlot := by omega
        have hlt' : 2 + preRounds + (challengeSpends - (rem' + 1)) <
            (if isDummy then pauseSlot + 1 else pauseSlot) := by
          cases isDummy <;> simp <;> omega
        simp only [heq, ↓reduceIte, hlt, hlt', ProbComp.eval_bind, PMF.bind_bind]
        refine pmfBind_congr _ fun rPrime => pmfBind_congr _ fun pi =>
          pmfBind_congr _ fun resp => ?_
        cases decide (resp.refund < env.bound) &&
            env.S.verify pk (env.tag (env.Com.eval env.ck
              ⟨env.dummyNf, ctx, 0⟩ rPrime) resp.refund) resp.sig
        · simp only [Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
            PMF.pure_bind, PMF.bind_const]
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          simpa only [ProbComp.eval_bind] using ih (by omega) (by omega)
            ⟨nfPrime, noteAct.bal + noteAct.ref - choice.debit, resp.refund⟩
            (balOther + refOther - choice.debit) resp.refund resp.st

/-- Pausing `preLoopPause` at `pauseSlot` and committing `msgReal` (`isDummy = false`) or
`msgDummy` (`isDummy = true`) reconstructs `preLoopSim` at cutoff `pauseSlot` or
`pauseSlot + 1`. -/
private lemma preLoopPause_resume_eq {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (b isDummy : Bool) (pauseSlot rem : ℕ) (hrem : rem ≤ preRounds)
    (hslot : 2 + (preRounds - rem) ≤ pauseSlot)
    (note0 note1 : SimNote Nullifier) (st : State) :
    ProbComp.eval (do
        let res ← preLoopPause env adv pk ctx b pauseSlot rem hrem note0 note1 st
        let r ← env.Com.openSample
        resumeAfterCom env adv pauseSlot res.cont
          (env.Com.eval env.ck (if isDummy then res.msgDummy else res.msgReal) r)) =
      ProbComp.eval (preLoopSim env adv pk ctx b
        (if isDummy then pauseSlot + 1 else pauseSlot) rem hrem note0 note1 st) := by
  induction rem generalizing note0 note1 st with
  | zero =>
    cases b
    · exact challengeLoopPause_resume_eq env adv pk ctx isDummy pauseSlot challengeSpends
        (le_refl _) (by omega) note0 note1.bal note1.ref st
    · exact challengeLoopPause_resume_eq env adv pk ctx isDummy pauseSlot challengeSpends
        (le_refl _) (by omega) note1 note0.bal note0.ref st
  | succ rem' ih =>
    simp only [preLoopPause, preLoopSim, ProbComp.eval_bind, PMF.bind_bind]
    refine pmfBind_congr _ fun choice => ?_
    set noteSel := if choice.client then note1 else note0
    cases spendAdmissible env.bound noteSel.bal noteSel.ref choice.debit
    · simp only [Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
        PMF.pure_bind, PMF.bind_const]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind,
        PMF.bind_bind]
      refine pmfBind_congr _ fun nfPrime => ?_
      by_cases heq : 2 + (preRounds - (rem' + 1)) = pauseSlot
      · have hrem_eq : preRounds - (preRounds - (rem' + 1) + 1) = rem' := by omega
        cases isDummy
        · simp only [heq, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.pure_bind, resumeAfterCom, hrem_eq, Nat.lt_irrefl, noteSel]
          refine pmfBind_congr _ fun rPrime => pmfBind_congr _ fun pi =>
            pmfBind_congr _ fun resp => congrArg ProbComp.eval ?_
          exact ite_congr rfl (fun _ => rfl) fun _ => preLoopSim_cutoff_congr env adv pk ctx b
            (pauseSlot + 1) pauseSlot rem' (by omega) (by omega) (by omega) _ _ _
        · simp only [heq, ↓reduceIte, Nat.lt_succ_self, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.pure_bind, resumeAfterCom, hrem_eq, noteSel]
      · have hlt : 2 + (preRounds - (rem' + 1)) < pauseSlot := by omega
        have hlt' : 2 + (preRounds - (rem' + 1)) <
            (if isDummy then pauseSlot + 1 else pauseSlot) := by
          cases isDummy <;> simp <;> omega
        simp only [heq, ↓reduceIte, hlt, hlt', ProbComp.eval_bind, PMF.bind_bind]
        refine pmfBind_congr _ fun rPrime => pmfBind_congr _ fun pi =>
          pmfBind_congr _ fun resp => ?_
        cases decide (resp.refund < env.bound) &&
            env.S.verify pk (env.tag (env.Com.eval env.ck
              ⟨env.dummyNf, ctx, 0⟩ rPrime) resp.refund) resp.sig
        · simp only [Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
            PMF.pure_bind, PMF.bind_const]
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          simpa only [ProbComp.eval_bind] using ih (by omega) (by omega)
            (if choice.client then note0
              else ⟨nfPrime, noteSel.bal + noteSel.ref - choice.debit, resp.refund⟩)
            (if choice.client
              then ⟨nfPrime, noteSel.bal + noteSel.ref - choice.debit, resp.refund⟩
              else note1)
            resp.st

/-- Full prefix `runPause` with `msgReal` (`isDummy = false`) or `msgDummy` (`isDummy = true`)
reconstructs `runSimProgram` at cutoff `pauseSlot` or `pauseSlot + 1`. -/
private lemma runPause_resume_eq {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (b isDummy : Bool) (pauseSlot : ℕ) :
    ProbComp.eval (do
        let res ← runPause env adv b pauseSlot
        let r ← env.Com.openSample
        resumeAfterCom env adv pauseSlot res.cont
          (env.Com.eval env.ck (if isDummy then res.msgDummy else res.msgReal) r)) =
      ProbComp.eval (runSimProgram env adv b (if isDummy then pauseSlot + 1 else pauseSlot)) := by
  simp only [runPause, runSimProgram, ProbComp.eval_bind, PMF.bind_bind]
  refine pmfBind_congr _ fun initOut => ?_
  cases decide (0 < initOut.t0) && decide (initOut.t0 < env.bound) &&
      decide (0 < initOut.t1) && decide (initOut.t1 < env.bound)
  · simp only [Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
      PMF.pure_bind, PMF.bind_const]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind,
      PMF.bind_bind]
    refine pmfBind_congr _ fun nf0 => ?_
    by_cases h0 : 0 = pauseSlot
    · subst pauseSlot
      cases isDummy
      · simp only [↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
          PMF.pure_bind, resumeAfterCom, Nat.lt_irrefl, Nat.not_lt_zero]
        refine pmfBind_congr _ fun r0 => pmfBind_congr _ fun pi0 => pmfBind_congr _ fun nf1 =>
          pmfBind_congr _ fun r1 => pmfBind_congr _ fun pi1 => pmfBind_congr _ fun issResp => ?_
        split_ifs
        · rfl
        · exact congrArg ProbComp.eval (preLoopSim_cutoff_congr env adv initOut.pk initOut.ctx b 1 0
            preRounds (le_refl _) (by omega) (by omega) _ _ _)
      · simp only [↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
          resumeAfterCom, show (0 : ℕ) < 1 by omega, eq_false (by omega : ¬((1 : ℕ) < 0 + 1))]
    · have h0lt' : 0 < (if isDummy then pauseSlot + 1 else pauseSlot) := by
        cases isDummy <;> simp
        omega
      simp only [h0, h0lt', ↓reduceIte, ProbComp.eval_bind, PMF.bind_bind]
      refine pmfBind_congr _ fun r0 => pmfBind_congr _ fun pi0 => pmfBind_congr _ fun nf1 => ?_
      by_cases h1 : 1 = pauseSlot
      · subst pauseSlot
        cases isDummy
        · simp only [↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.pure_bind, resumeAfterCom, Nat.lt_irrefl]
          refine pmfBind_congr _ fun r1 => pmfBind_congr _ fun pi1 =>
            pmfBind_congr _ fun issResp => ?_
          split_ifs
          · rfl
          · exact congrArg ProbComp.eval (preLoopSim_cutoff_congr env adv initOut.pk initOut.ctx b
              2 1 preRounds (le_refl _) (by omega) (by omega) _ _ _)
        · simp only [↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
            resumeAfterCom, show (1 : ℕ) < 2 by omega]
      · have h1lt' : 1 < (if isDummy then pauseSlot + 1 else pauseSlot) := by
          cases isDummy <;> simp <;> omega
        simp only [h1, h1lt', ↓reduceIte, ProbComp.eval_bind, PMF.bind_bind]
        refine pmfBind_congr _ fun r1 => pmfBind_congr _ fun pi1 =>
          pmfBind_congr _ fun issResp => ?_
        cases env.S.verify initOut.pk (env.tag (env.Com.eval env.ck
              ⟨env.dummyNf, initOut.ctx, 0⟩ r0) 0) issResp.s0 &&
            env.S.verify initOut.pk (env.tag (env.Com.eval env.ck
              ⟨env.dummyNf, initOut.ctx, 0⟩ r1) 0) issResp.s1
        · simp only [Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
            PMF.pure_bind, PMF.bind_const]
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          simpa only [ProbComp.eval_bind] using
            preLoopPause_resume_eq env adv initOut.pk initOut.ctx b isDummy pauseSlot
              preRounds (le_refl _) (by omega) ⟨nf0, initOut.t0, 0⟩ ⟨nf1, initOut.t1, 0⟩
              issResp.st

/-- Full prefix `runPause` with `msgReal` reconstructs `runSimProgram` at cutoff `pauseSlot`. -/
private lemma runPause_real_eq {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (b : Bool) (pauseSlot : ℕ) :
    ProbComp.eval (do
        let res ← runPause env adv b pauseSlot
        let r ← env.Com.openSample
        resumeAfterCom env adv pauseSlot res.cont (env.Com.eval env.ck res.msgReal r)) =
      ProbComp.eval (runSimProgram env adv b pauseSlot) :=
  runPause_resume_eq env adv b false pauseSlot

/-- Full prefix `runPause` with `msgDummy` reconstructs `runSimProgram` at `pauseSlot + 1`. -/
private lemma runPause_dummy_eq {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (b : Bool) (pauseSlot : ℕ) :
    ProbComp.eval (do
        let res ← runPause env adv b pauseSlot
        let r ← env.Com.openSample
        resumeAfterCom env adv pauseSlot res.cont (env.Com.eval env.ck res.msgDummy r)) =
      ProbComp.eval (runSimProgram env adv b (pauseSlot + 1)) :=
  runPause_resume_eq env adv b true pauseSlot

/-- Private state preserved across the two stages of `unlinkHidingReduction`. -/
structure UnlinkHidingState
    (CommitKey PK Context C Nullifier Proof State : Type)
    (preRounds challengeSpends : ℕ) where
  /-- Commitment key `ck`. -/
  ck : CommitKey
  /-- Sampled dummy nullifier used across dummy-message commitment slots. -/
  dummyNf : Nullifier
  /-- Sampled challenge bit `b`. -/
  b : Bool
  /-- Sampled commitment hybrid slot `hop`. -/
  hop : Fin (2 + preRounds + challengeSpends)
  /-- Continuation frozen immediately before commitment slot `hop`. -/
  cont : SimContinuation PK Context C Nullifier Proof State preRounds challengeSpends

/-- Commutes two independent leading `PMF.bind` draws past a third `PMF.bind`. -/
private lemma pmfBind_comm2 {α β γ δ : Type} (p : PMF α) (q : PMF β) (r : PMF γ)
    (k : α → β → γ → PMF δ) :
    (p.bind fun a => q.bind fun b => r.bind fun c => k a b c) =
      r.bind fun c => p.bind fun a => q.bind fun b => k a b c := by
  conv_lhs => enter [2, a]; rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- Explicit `TwoStage` commitment-hiding reduction for the adaptive unlinkability reduction
(concrete query-bounded step, `#7068`): samples `dummyNf ← nfGen`, uniform challenge bit
`b ← Bool`, and random commitment hybrid slot `hop ← Fin (2 + preRounds + challengeSpends)`, runs
the simulator up to `hop`, submits `(msgReal, msgDummy)` to `Com.toScheme`, and tests whether the
resumed adversary guesses `b`. -/
noncomputable def unlinkHidingReduction {preRounds challengeSpends : ℕ}
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends) :
    TwoStage CommitKey (MessagePair (CommitMsg Nullifier Context)) C Bool
      (UnlinkHidingState CommitKey PK Context C Nullifier Proof State
        preRounds challengeSpends) where
  choose ck := do
    have : NeZero (2 + preRounds + challengeSpends) := ⟨by omega⟩
    let dummyNf ← nfGen
    let b ← ProbComp.uniform Bool
    let hop ← ProbComp.uniform (Fin (2 + preRounds + challengeSpends))
    let env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof :=
      ⟨Com, nfGen, tag, S, bound, sys, ck, dummyNf⟩
    let res ← runPause env adv b hop.val
    return (⟨res.msgReal, res.msgDummy⟩, ⟨ck, dummyNf, b, hop, res.cont⟩)
  guess st cStar := do
    let env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof :=
      ⟨Com, nfGen, tag, S, bound, sys, st.ck, st.dummyNf⟩
    let g ← resumeAfterCom env adv st.hop.val st.cont cStar
    return decide (g = st.b)

/-- Skeleton of the challenge loop at the final hybrid `hop = 2 + preRounds + challengeSpends`,
sampling fresh `nf` on the fly at each spend without inspecting `balAct` or `balOther`. -/
private def challengeLoopG4Skeleton {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (rem : ℕ) (hrem : rem ≤ challengeSpends)
    (balAct refAct balOther refOther : ℕ) (st : State) : ProbComp Bool :=
  match rem with
  | 0 => adv.guess st
  | rem' + 1 =>
    let j : Fin challengeSpends := ⟨challengeSpends - (rem' + 1), by omega⟩
    do
      let choice ← adv.chooseChallenge j st
      let okAct := spendAdmissible env.bound balAct refAct choice.debit
      let okOther := spendAdmissible env.bound balOther refOther choice.debit
      if !(okAct && okOther) then
        return false
      else
        let nfAct ← env.nfGen
        let rPrime ← env.Com.openSample
        let cPrime := env.Com.eval env.ck ⟨env.dummyNf, ctx, 0⟩ rPrime
        let pi ← env.sys.simulate env.ck (.spend ⟨pk, ctx, nfAct, choice.debit, cPrime⟩)
        let resp ← adv.finalizeChallenge j choice.st nfAct choice.debit cPrime pi
        if !(resp.refund < env.bound &&
            env.S.verify pk (env.tag cPrime resp.refund) resp.sig) then
          return false
        else
          challengeLoopG4Skeleton env adv pk ctx rem' (by omega)
            (balAct + refAct - choice.debit) resp.refund
            (balOther + refOther - choice.debit) resp.refund resp.st

/-- Symmetry of `challengeLoopG4Skeleton` under swapping the active and inactive client balances
`(bal0, ref0) ↔ (bal1, ref1)`. -/
private lemma challengeLoopG4Skeleton_symm {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (rem : ℕ) (hrem : rem ≤ challengeSpends)
    (bal0 ref0 bal1 ref1 : ℕ) (st : State) :
    challengeLoopG4Skeleton env adv pk ctx rem hrem bal0 ref0 bal1 ref1 st =
      challengeLoopG4Skeleton env adv pk ctx rem hrem bal1 ref1 bal0 ref0 st := by
  induction rem generalizing bal0 ref0 bal1 ref1 st with
  | zero => rfl
  | succ rem' ih =>
    simp only [challengeLoopG4Skeleton]
    congr 1 with choice
    have hcomm : (spendAdmissible env.bound bal0 ref0 choice.debit &&
        spendAdmissible env.bound bal1 ref1 choice.debit) =
        (spendAdmissible env.bound bal1 ref1 choice.debit &&
        spendAdmissible env.bound bal0 ref0 choice.debit) := Bool.and_comm _ _
    simp only [hcomm]
    split_ifs
    · rfl
    · congr 1 with nfAct; congr 1 with rPrime; congr 1 with pi; congr 1 with resp
      split_ifs
      · rfl
      · exact ih (by omega) _ _ _ _ _

/-- Equivalence pulling fresh unused `nfAct` out to the front of `challengeLoopSim` at the final
hybrid `hop = 2 + preRounds + challengeSpends`. -/
private lemma challengeLoopSim_G4_eq_skeleton {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (rem : ℕ) (hrem : rem ≤ challengeSpends)
    (balAct refAct balOther refOther : ℕ) (st : State) :
    ((ProbComp.eval env.nfGen).bind fun nfAct =>
      ProbComp.eval (challengeLoopSim env adv pk ctx (2 + preRounds + challengeSpends) rem
        hrem ⟨nfAct, balAct, refAct⟩ balOther refOther st)) =
      ProbComp.eval (challengeLoopG4Skeleton env adv pk ctx rem hrem balAct refAct balOther
        refOther st) := by
  induction rem generalizing balAct refAct balOther refOther st with
  | zero =>
    simp [challengeLoopSim, challengeLoopG4Skeleton, PMF.bind_const]
  | succ rem' ih =>
    have hlt : 2 + preRounds + (challengeSpends - (rem' + 1)) <
        2 + preRounds + challengeSpends := by omega
    simp only [challengeLoopSim, challengeLoopG4Skeleton, hlt, ↓reduceIte, ProbComp.eval_bind]
    rw [PMF.bind_comm]
    refine pmfBind_congr _ fun choice => ?_
    split_ifs with hguard
    · simp [ProbComp.eval_pure, PMF.bind_const]
    · simp only [ProbComp.eval_bind]
      refine pmfBind_congr _ fun nfAct => ?_
      rw [PMF.bind_comm]
      refine pmfBind_congr _ fun rPrime => ?_
      rw [PMF.bind_comm]
      refine pmfBind_congr _ fun pi => ?_
      rw [PMF.bind_comm]
      refine pmfBind_congr _ fun resp => ?_
      split_ifs with hfin
      · simp [ProbComp.eval_pure, PMF.bind_const]
      · exact ih (by omega) _ _ _ _ _

/-- Pre-challenge skeleton at the final hybrid `hop = 2 + preRounds + challengeSpends`. -/
private def preLoopG4Skeleton {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (rem : ℕ) (hrem : rem ≤ preRounds)
    (bal0 ref0 bal1 ref1 : ℕ) (st : State) : ProbComp Bool :=
  match rem with
  | 0 => challengeLoopG4Skeleton env adv pk ctx challengeSpends (le_refl _)
      bal0 ref0 bal1 ref1 st
  | rem' + 1 =>
    let i : Fin preRounds := ⟨preRounds - (rem' + 1), by omega⟩
    do
      let choice ← adv.choosePre i st
      let balSel := if choice.client then bal1 else bal0
      let refSel := if choice.client then ref1 else ref0
      if !spendAdmissible env.bound balSel refSel choice.debit then
        return false
      else
        let nfSel ← env.nfGen
        let rPrime ← env.Com.openSample
        let cPrime := env.Com.eval env.ck ⟨env.dummyNf, ctx, 0⟩ rPrime
        let pi ← env.sys.simulate env.ck (.spend ⟨pk, ctx, nfSel, choice.debit, cPrime⟩)
        let resp ← adv.finalizePre i choice.st nfSel choice.debit cPrime pi
        if !(resp.refund < env.bound &&
            env.S.verify pk (env.tag cPrime resp.refund) resp.sig) then
          return false
        else
          let balNext := balSel + refSel - choice.debit
          let bal0' := if choice.client then bal0 else balNext
          let ref0' := if choice.client then ref0 else resp.refund
          let bal1' := if choice.client then balNext else bal1
          let ref1' := if choice.client then resp.refund else ref1
          preLoopG4Skeleton env adv pk ctx rem' (by omega) bal0' ref0' bal1' ref1' resp.st

/-- Equivalence pulling both unused nullifiers `(nf0, nf1)` through `preLoopSim` at the final
hybrid `hop = 2 + preRounds + challengeSpends`, independently of `b`. -/
private lemma preLoopSim_G4_eq_skeleton {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends)
    (pk : PK) (ctx : Context) (b : Bool) (rem : ℕ) (hrem : rem ≤ preRounds)
    (bal0 ref0 bal1 ref1 : ℕ) (st : State) :
    ((ProbComp.eval env.nfGen).bind fun nf0 => (ProbComp.eval env.nfGen).bind fun nf1 =>
      ProbComp.eval (preLoopSim env adv pk ctx b (2 + preRounds + challengeSpends) rem hrem
        ⟨nf0, bal0, ref0⟩ ⟨nf1, bal1, ref1⟩ st)) =
      ProbComp.eval (preLoopG4Skeleton env adv pk ctx rem hrem bal0 ref0 bal1 ref1 st) := by
  induction rem generalizing bal0 ref0 bal1 ref1 st with
  | zero =>
    simp only [preLoopSim, preLoopG4Skeleton]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hsub := challengeLoopSim_G4_eq_skeleton env adv pk ctx challengeSpends
        (le_refl _) bal0 ref0 bal1 ref1 st
      simpa only [PMF.bind_const] using hsub
    · simp only [↓reduceIte]
      have hsub := challengeLoopSim_G4_eq_skeleton env adv pk ctx challengeSpends
        (le_refl _) bal1 ref1 bal0 ref0 st
      rw [PMF.bind_const, hsub]
      exact congrArg ProbComp.eval (challengeLoopG4Skeleton_symm env adv pk ctx challengeSpends
        (le_refl _) bal1 ref1 bal0 ref0 st)
  | succ rem' ih =>
    have hlt : 2 + (preRounds - (rem' + 1)) < 2 + preRounds + challengeSpends := by omega
    simp only [preLoopSim, preLoopG4Skeleton, hlt, ↓reduceIte, ProbComp.eval_bind]
    rw [pmfBind_comm2]
    refine pmfBind_congr _ fun choice => ?_
    cases choice.client
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases spendAdmissible env.bound bal0 ref0 choice.debit
      · simp only [Bool.not_false, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind]
        refine pmfBind_congr _ fun nf0 => ?_
        rw [pmfBind_comm2]
        refine pmfBind_congr _ fun rPrime => ?_
        rw [pmfBind_comm2]
        refine pmfBind_congr _ fun pi => ?_
        rw [pmfBind_comm2]
        refine pmfBind_congr _ fun resp => ?_
        split_ifs
        · simp [ProbComp.eval_pure, PMF.bind_const]
        · rw [PMF.bind_comm]
          exact ih (by omega) _ _ _ _ _
    · simp only [↓reduceIte]
      cases spendAdmissible env.bound bal1 ref1 choice.debit
      · simp only [Bool.not_false, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind]
        rw [PMF.bind_comm]
        refine pmfBind_congr _ fun nf1 => ?_
        rw [pmfBind_comm2]
        refine pmfBind_congr _ fun rPrime => ?_
        rw [pmfBind_comm2]
        refine pmfBind_congr _ fun pi => ?_
        rw [pmfBind_comm2]
        refine pmfBind_congr _ fun resp => ?_
        split_ifs
        · simp [ProbComp.eval_pure, PMF.bind_const]
        · exact ih (by omega) _ _ _ _ _

/-- At the final hybrid `hop = 2 + preRounds + challengeSpends` (`G4`), the two challenge-bit
worlds are identically distributed (`G4 false = G4 true`). -/
private lemma g4_false_eq_true {preRounds challengeSpends : ℕ}
    (env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends) :
    ProbComp.eval (runSimProgram env adv false (2 + preRounds + challengeSpends)) =
      ProbComp.eval (runSimProgram env adv true (2 + preRounds + challengeSpends)) := by
  have heq (b : Bool) :
      ProbComp.eval (runSimProgram env adv b (2 + preRounds + challengeSpends)) =
      ProbComp.eval (do
        let initOut ← adv.init env.ck
        if !(0 < initOut.t0 && initOut.t0 < env.bound &&
            0 < initOut.t1 && initOut.t1 < env.bound) then
          return false
        else
          let dummyMsg : CommitMsg Nullifier Context := ⟨env.dummyNf, initOut.ctx, 0⟩
          let r0 ← env.Com.openSample
          let c0 := env.Com.eval env.ck dummyMsg r0
          let pi0 ← env.sys.simulate env.ck (.issue ⟨initOut.ctx, c0, initOut.t0⟩)
          let r1 ← env.Com.openSample
          let c1 := env.Com.eval env.ck dummyMsg r1
          let pi1 ← env.sys.simulate env.ck (.issue ⟨initOut.ctx, c1, initOut.t1⟩)
          let issResp ← adv.issue initOut.st c0 pi0 c1 pi1
          if !(env.S.verify initOut.pk (env.tag c0 0) issResp.s0 &&
              env.S.verify initOut.pk (env.tag c1 0) issResp.s1) then
            return false
          else
            preLoopG4Skeleton env adv initOut.pk initOut.ctx preRounds (le_refl _)
              initOut.t0 0 initOut.t1 0 issResp.st) := by
    have h0 : 0 < 2 + preRounds + challengeSpends := by omega
    have h1 : 1 < 2 + preRounds + challengeSpends := by omega
    simp only [runSimProgram, h0, h1, ↓reduceIte, ProbComp.eval_bind]
    refine pmfBind_congr _ fun initOut => ?_
    split_ifs
    · rfl
    · simp only [ProbComp.eval_bind]
      rw [PMF.bind_comm]
      refine pmfBind_congr _ fun r0 => ?_
      rw [PMF.bind_comm]
      refine pmfBind_congr _ fun pi0 => ?_
      rw [pmfBind_comm2]
      refine pmfBind_congr _ fun r1 => ?_
      rw [pmfBind_comm2]
      refine pmfBind_congr _ fun pi1 => ?_
      rw [pmfBind_comm2]
      refine pmfBind_congr _ fun issResp => ?_
      split_ifs
      · simp [ProbComp.eval_pure, PMF.bind_const]
      · exact preLoopSim_G4_eq_skeleton env adv initOut.pk initOut.ctx b preRounds (le_refl _)
          initOut.t0 0 initOut.t1 0 issResp.st
  rw [heq false, heq true]

/-- Adaptive malicious-issuer unlinkability reduction step (`#7068`), original to this library as
a finite query-bounded bound for `[VOLEACT2026]` (`#issuance` and `#spending`; `[VOLEACT2026]`
`#proof-status` leaves unlinkability open): for any adaptive adversary `adv` against
`unlinkabilityExperiment`,
`Adv^unlink ≤ 2 * Adv^ZK + 2 * (2 + preRounds + challengeSpends) * Adv^hide`
via `zkDistinguisher` and `unlinkHidingReduction`.
When `preRounds = 0`, the hiding factor specializes directly to `2 * (2 + challengeSpends)`.
The leading factor of `2` converts the `[0, 1]` two-world `Game.advantage` into `[0, 1/2]`
bit-guessing bias via `Game.advantage_le_two_mul_uniform_bool_xor`, and replacing all
`2 + preRounds + challengeSpends` emitted commitments sequentially via
`Game.advantage_hybrid_average` avoids guessing which pre-challenge spend terminates each client's
branch under adaptive `choosePre` (asymptotic certificates remain open under `#7068`). -/
theorem unlinkabilityExperiment_advantage_le [DecidableEq C] {preRounds challengeSpends : ℕ}
    (Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C O)
    (nfGen : ProbComp Nullifier)
    (tag : C → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (bound : ℕ)
    (sys : ProverSystem CommitKey PK C Context Nullifier O Sig Proof)
    (adv : UnlinkAdversary CommitKey PK Context C Nullifier Proof Sig State
      preRounds challengeSpends) :
    (Game.advantage
      (unlinkabilityExperiment Com nfGen tag S bound sys adv false)
      (unlinkabilityExperiment Com nfGen tag S bound sys adv true) : ℝ) ≤
      2 * (Game.advantage
        (multiProofZKRealGame Com tag S bound sys (zkDistinguisher Com nfGen tag S bound adv))
        (multiProofZKSimGame Com tag S bound sys (zkDistinguisher Com nfGen tag S bound adv)) :
          ℝ) +
        2 * ((2 + preRounds + challengeSpends : ℕ) : ℝ) *
          (Experiment.advantage
            (Com.toScheme.hidingExperiment
              (unlinkHidingReduction Com nfGen tag S bound sys adv) false)
            (Com.toScheme.hidingExperiment
              (unlinkHidingReduction Com nfGen tag S bound sys adv) true) : ℝ) := by
  let N := 2 + preRounds + challengeSpends
  let bitGame : (CommitKey → Bool → ProbComp Bool) → Game := fun fn =>
    ProbComp.eval do
      let ck ← Com.keyGen
      let b ← ProbComp.uniform Bool
      let g ← fn ck b
      return decide (g = b)
  let envOf : CommitKey → Nullifier →
      SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof :=
    fun ck dummyNf => ⟨Com, nfGen, tag, S, bound, sys, ck, dummyNf⟩
  let g0Fn : CommitKey → Bool → ProbComp Bool := fun ck b =>
    (unlinkOracleProgram Com nfGen tag S bound adv true b ck).run
      (realProofOracle Com tag S bound sys ck)
  let hybFn : ℕ → Game := fun h =>
    (ProbComp.eval nfGen).bind fun dummyNf =>
      bitGame (fun ck b => runSimProgram (envOf ck dummyNf) adv b h)
  let g0 : Bool → Game := fun b =>
    unlinkabilityExperiment Com nfGen tag S bound sys adv b
  let g4 : Bool → Game := fun b =>
    (ProbComp.eval nfGen).bind fun dummyNf =>
      ProbComp.eval (Com.keyGen >>= fun ck => runSimProgram (envOf ck dummyNf) adv b N)
  have hzkReal : multiProofZKRealGame Com tag S bound sys
      (zkDistinguisher Com nfGen tag S bound adv) = bitGame g0Fn := by
    simp only [multiProofZKRealGame, zkDistinguisher, bitGame, g0Fn, ProbOracleComp.run_bind,
      ProbOracleComp.run_sample, ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure]
  have hzkSim : multiProofZKSimGame Com tag S bound sys
      (zkDistinguisher Com nfGen tag S bound adv) = hybFn 0 := by
    simp only [hybFn, multiProofZKSimGame, zkDistinguisher, bitGame, ProbOracleComp.run_bind,
      ProbOracleComp.run_sample, ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure]
    have hstep : ∀ dummyNf,
        ((ProbComp.eval Com.keyGen).bind fun ck =>
          (uniformOfFintype Bool).bind fun b =>
            (ProbComp.eval (runSimProgram (envOf ck dummyNf) adv b 0)).bind fun g =>
              PMF.pure (decide (g = b))) =
        ((ProbComp.eval Com.keyGen).bind fun ck =>
          (uniformOfFintype Bool).bind fun b =>
            (ProbComp.eval ((unlinkOracleProgram Com nfGen tag S bound adv true b ck).run
              (simProofOracle Com tag S bound sys ck))).bind fun g =>
              PMF.pure (decide (g = b))) := by
      intro dummyNf
      refine pmfBind_congr _ fun ck => pmfBind_congr _ fun b => ?_
      rw [← unlinkOracleProgram_sim_eq (envOf ck dummyNf) adv b]
    simp_rw [hstep, PMF.bind_const]
  have hg4_eq : g4 false = g4 true := by
    refine pmfBind_congr _ fun dummyNf => ?_
    simp only [ProbComp.eval_bind]
    exact pmfBind_congr _ fun ck => g4_false_eq_true (envOf ck dummyNf) adv
  have hhide_eq (bHide : Bool) :
      ProbComp.eval (Com.toScheme.hidingExperiment
        (unlinkHidingReduction Com nfGen tag S bound sys adv) bHide) =
        (uniformOfFintype (Fin N)).bind (fun h : Fin N =>
          hybFn (if bHide then h.val + 1 else h.val)) := by
    have : NeZero N := ⟨by omega⟩
    simp only [Commitment.Scheme.eval_hidingExperiment, Game.withSetup, eval_lrExperiment,
      unlinkHidingReduction, OpeningCommitment.toScheme, Commitment.Scheme.commitment, hybFn,
      bitGame, envOf, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def, ite_true]
    rw [PMF.bind_comm]
    conv_rhs => rw [PMF.bind_comm]
    refine pmfBind_congr _ fun dummyNf => ?_
    conv_rhs => rw [PMF.bind_comm]
    refine pmfBind_congr _ fun ck => ?_
    rw [PMF.bind_comm]
    refine pmfBind_congr _ fun h => pmfBind_congr _ fun b => ?_
    cases bHide
    · simp only [MessagePair.select_false, Bool.false_eq_true, ↓reduceIte]
      have hreal := runPause_real_eq (envOf ck dummyNf) adv b h.val
      calc _ = ((ProbComp.eval (do
              let res ← runPause (envOf ck dummyNf) adv b h.val
              let r ← Com.openSample
              resumeAfterCom (envOf ck dummyNf) adv h.val res.cont
                (Com.eval ck res.msgReal r))).bind fun g => PMF.pure (decide (g = b))) := by
            simp only [envOf, ProbComp.eval_bind, PMF.bind_bind]
        _ = _ := by rw [hreal]
    · simp only [MessagePair.select_true, ↓reduceIte]
      have hdummy := runPause_dummy_eq (envOf ck dummyNf) adv b h.val
      calc _ = ((ProbComp.eval (do
              let res ← runPause (envOf ck dummyNf) adv b h.val
              let r ← Com.openSample
              resumeAfterCom (envOf ck dummyNf) adv h.val res.cont
                (Com.eval ck res.msgDummy r))).bind fun g => PMF.pure (decide (g = b))) := by
            simp only [envOf, ProbComp.eval_bind, PMF.bind_bind]
        _ = _ := by rw [hdummy]
  have hxor_not (fn : Bool → Game) :
      ((uniformOfFintype Bool).bind fun b => (fn b).map (fun g => g ^^ b)).map Bool.not =
        (uniformOfFintype Bool).bind fun b => (fn b).map (fun g => decide (g = b)) := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    refine pmfBind_congr _ fun b => ?_
    congr 1 with g
    cases g <;> cases b <;> rfl
  have hxor0 : ((uniformOfFintype Bool).bind fun b => (g0 b).map (fun g => g ^^ b)).map Bool.not =
      bitGame g0Fn := by
    rw [hxor_not g0]
    simp only [bitGame, g0, unlinkabilityExperiment, g0Fn, ProbComp.eval_bind,
      ProbComp.eval_uniform, ProbComp.eval_pure, PMF.map, Function.comp_def, PMF.bind_bind]
    rw [PMF.bind_comm]
  have hxor4 : ((uniformOfFintype Bool).bind fun b => (g4 b).map (fun g => g ^^ b)).map Bool.not =
      hybFn N := by
    rw [hxor_not g4]
    simp only [hybFn, g4, bitGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
      PMF.map, Function.comp_def, PMF.bind_bind]
    rw [PMF.bind_comm]
    refine pmfBind_congr _ fun dummyNf => ?_
    rw [PMF.bind_comm]
  have hxor_bound := Game.advantage_le_two_mul_uniform_bool_xor g0 g4
  rw [← Game.advantage_not _ ((uniformOfFintype Bool).bind fun b => (g4 b).map fun g => g ^^ b),
    hxor0, hxor4, hg4_eq, Game.advantage_self, add_zero] at hxor_bound
  have : NeZero N := ⟨by omega⟩
  have hhybSide (bHide : Bool) :
      ((uniformOfFintype (Fin N)).bind fun i =>
        if i.val < N then hybFn (if bHide then i.val + 1 else i.val) else PMF.pure false) =
      ProbComp.eval (Com.toScheme.hidingExperiment
        (unlinkHidingReduction Com nfGen tag S bound sys adv) bHide) := by
    rw [hhide_eq bHide]
    exact pmfBind_congr _ fun i => ite_eq_left i.isLt
  have hhyb := Game.advantage_hybrid_average hybFn N N le_rfl
  have hhybL := by simpa only [Bool.false_eq_true, ↓reduceIte] using hhybSide false
  have hhybR := by simpa only [↓reduceIte] using hhybSide true
  rw [hhybL, hhybR] at hhyb
  have htri : Game.advantage (bitGame g0Fn) (hybFn N) ≤
      Game.advantage
        (multiProofZKRealGame Com tag S bound sys (zkDistinguisher Com nfGen tag S bound adv))
        (multiProofZKSimGame Com tag S bound sys (zkDistinguisher Com nfGen tag S bound adv)) +
      (N : ℝ≥0) * Experiment.advantage
        (Com.toScheme.hidingExperiment
          (unlinkHidingReduction Com nfGen tag S bound sys adv) false)
        (Com.toScheme.hidingExperiment
          (unlinkHidingReduction Com nfGen tag S bound sys adv) true) := by
    rw [← hhyb, hzkReal, hzkSim]
    exact Game.advantage_triangle _ _ _
  have hle_nn : Game.advantage (g0 false) (g0 true) ≤
      2 * Game.advantage
        (multiProofZKRealGame Com tag S bound sys (zkDistinguisher Com nfGen tag S bound adv))
        (multiProofZKSimGame Com tag S bound sys (zkDistinguisher Com nfGen tag S bound adv)) +
      2 * (N : ℝ≥0) * Experiment.advantage
        (Com.toScheme.hidingExperiment
          (unlinkHidingReduction Com nfGen tag S bound sys adv) false)
        (Com.toScheme.hidingExperiment
          (unlinkHidingReduction Com nfGen tag S bound sys adv) true) := by
    calc Game.advantage (g0 false) (g0 true)
        ≤ 2 * Game.advantage (bitGame g0Fn) (hybFn N) := hxor_bound
      _ ≤ 2 * (Game.advantage _ _ + (N : ℝ≥0) * Experiment.advantage _ _) :=
          mul_le_mul_of_nonneg_left htri zero_le
      _ = _ := by ring
  exact_mod_cast hle_nn

end UnlinkabilityReductionContinuation

end Cslib.Crypto.AnonymousToken.Unlinkability
