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
public import CslibFrontier.Crypto.Protocols.AnonymousToken.CRTHazard
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
public import CslibFrontier.Languages.Probabilistic.UntilBad
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import Mathlib.Algebra.CharP.Two

/-!
# Malicious-issuer unlinkability and non-black-box CRT decoupling for VOLE-ACT

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
4. **Non-black-box `G8 → G8.5` CRT witness-reuse decoupling (`crtDecouple_advantage_le`)**:
   connecting the coupled CRT witness-reuse simulation `g8Game` (`G8` in [BaumEtAl2026FAEST]
   §10.10 Theorem 10.42; `d_j = r_j + u_j`, raw `H5`-derived `cmult`) via `IdenticalUntilBad` to
   decoupled `g85Game` (`G8.5` is this library's intermediate hop), and reducing `BadH5` via
   `badH5HidingReduction` and `badH5BindingReduction` (using provably distinct `CommitMsg.bumpBal`)
   to `qTok * (Adv^hide + Pr[binding]) + g85IvCollisionProb` (original to this library). Here token
   messages are non-adaptive (fixed by `ck`), `r j` itself serves as the witness prefix (`r`-first
   layout), `cmult` is raw `H5` output, `g85IvCollisionProb` replaces the fixed `2 ^ (-λ)` term,
   and end-to-end composition from `G1–G8` remains open under `#7068`.

As in `CRTHazard.lean`, all games and reductions are finite query-bounded constructions (`#7068`);
asymptotic polynomial-time certificates are outside this module's scope.

## Main definitions

* `OpeningCommitment`, `OpeningCommitment.toScheme`: deterministic-evaluation opening commitment.
* `CommitMsg`, `CommitMsg.bumpBal`, `IssueStmt`, `IssueWit`, `SpendStmt`, `SpendWit`,
  `ProofStatement`, `ProofWitness`, `validStatement`, `ProverSystem`, `multiProofZKRealGame`,
  `multiProofZKSimGame`.
* `UnlinkAdversary`, `unlinkabilityExperiment`, `unguardedUnlinkabilityExperiment`.
* `balancePartitionInitAdversary`, `balancePartitionRefundAdversary`.
* `zkDistinguisher`, `unlinkHidingReduction`.
* `G85Setup`, `g8Game`, `g85Game`, `badH5HidingReduction`, `badH5BindingReduction`.

## Main results

* `OpeningCommitment.toScheme_correct`, `CommitMsg.bumpBal_ne`.
* `balancePartitionInit_unguarded_advantage_eq_one`,
  `balancePartitionInit_guarded_advantage_eq_zero`,
  `balancePartitionRefund_unguarded_advantage_eq_one`,
  `balancePartitionRefund_guarded_advantage_eq_zero`.
* `zkDistinguisher_isQueryBounded`, `unlinkabilityExperiment_advantage_le`.
* `crtDecouple_identicalUntilBad`, `crtDecouple_advantage_le`.

## References

* [*VOLE-ACT*][VOLEACT2026], Protocol Specification / Initial Issuance (`#issuance`), Spending
  (`#spending`), and Proof Status (`#proof-status`).
* [*FAEST v3: Algorithm Specifications*][BaumEtAl2026FAEST], Sections 3.1–3.3 (pp. 13–18),
  Section 6 (pp. 35–43, Figures 6.1–6.3), and Section 10.10 (Theorem 10.42, Games `G6`–`G11`,
  pp. 115–121).
-/

@[expose] public section

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
def OpeningCommitment.toScheme {CommitKey Message C Opening : Type}
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
def CommitMsg.bumpBal {Nullifier Context : Type} (m : CommitMsg Nullifier Context) :
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
def validStatement {CommitKey PK C Context Nullifier O Sig Target SK : Type}
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
def realProofOracle
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
def spendAdmissible (bound bal ref d : ℕ) : Bool :=
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
def ClientNote.toSim {Nullifier C O Sig : Type}
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
structure PauseResult
    (PK Context C Nullifier Proof State : Type) (preRounds challengeSpends : ℕ) where
  /-- Real note message submitted as left hiding challenge. -/
  msgReal : CommitMsg Nullifier Context
  /-- Dummy note message submitted as right hiding challenge. -/
  msgDummy : CommitMsg Nullifier Context
  /-- Continuation resuming execution after receiving challenge commitment `cStar`. -/
  cont : SimContinuation PK Context C Nullifier Proof State preRounds challengeSpends

section UnlinkPrograms

/-- Challenge-spend loop inside `ProbOracleComp (ProofSpec ...) Bool`. -/
def challengeLoopOracle
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
def preLoopOracle
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
def unlinkOracleProgram
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
noncomputable def unlinkabilityExperiment
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
    cases b
    · simp only [preLoopOracle, Bool.false_eq_true, ↓reduceIte] at htail ⊢
      simp only [htail ck, PMF.bind_const]
    · simp only [preLoopOracle, ↓reduceIte] at htail ⊢
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
  have hside : ∀ b : Bool,
      unguardedUnlinkabilityExperiment Com nfGen tag S bound sys adv b = PMF.pure (!b) := by
    intro b
    simp only [unguardedUnlinkabilityExperiment, ProbComp.eval_bind]
    trans (ProbComp.eval Com.keyGen).bind fun _ => PMF.pure (!b)
    · refine pmfBind_congr _ fun ck => ?_
      rw [eval_unlinkOracleProgram_mkSig_issue Com nfGen tag S bound sys adv pk ctx 2 2 mkSig
        (by omega) (by omega) hmksig (fun _ => rfl) (fun _ _ _ _ _ => rfl) false b ck]
      have hstep : ∀ nf0 r0 nf1 r1,
          ProbComp.eval ((preLoopOracle Com nfGen tag S bound adv ck pk ctx false b 2
            (by omega)
            ⟨nf0, 2, r0, Com.eval ck ⟨nf0, ctx, 2⟩ r0, 0,
              mkSig (tag (Com.eval ck ⟨nf0, ctx, 2⟩ r0) 0)⟩
            ⟨nf1, 2, r1, Com.eval ck ⟨nf1, ctx, 2⟩ r1, 0,
              mkSig (tag (Com.eval ck ⟨nf1, ctx, 2⟩ r1) 0)⟩ ()).run
            (realProofOracle Com tag S bound sys ck)) = PMF.pure (!b) := by
        intro nf0 r0 nf1 r1
        rw [eval_refund_preLoopOracle Com nfGen tag S bound sys hbound pk ctx mkSig hmksig ck
          false b nf0 nf1 r0 r1]
        have hchal : ∀ nf0' r0' nf1' r1',
            ProbComp.eval ((preLoopOracle Com nfGen tag S bound adv ck pk ctx false b 0
              (by omega)
              ⟨nf0', 1, r0', Com.eval ck ⟨nf0', ctx, 1⟩ r0', 2,
                mkSig (tag (Com.eval ck ⟨nf0', ctx, 1⟩ r0') 2)⟩
              ⟨nf1', 1, r1', Com.eval ck ⟨nf1', ctx, 1⟩ r1', 0,
                mkSig (tag (Com.eval ck ⟨nf1', ctx, 1⟩ r1') 0)⟩ ()).run
              (realProofOracle Com tag S bound sys ck)) = PMF.pure (!b) := by
          intro nf0' r0' nf1' r1'
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
        dsimp only [adv] at hchal
        simp only [hchal, PMF.bind_const]
      simp only [hstep, PMF.bind_const]
    · simp only [PMF.bind_const]
  have hfalse :
      unguardedUnlinkabilityExperiment Com nfGen tag S bound sys adv false = PMF.pure true :=
    hside false
  have htrue :
      unguardedUnlinkabilityExperiment Com nfGen tag S bound sys adv true = PMF.pure false :=
    hside true
  rw [hfalse, htrue]
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
      PMF.pure false := by
    simp only [unlinkabilityExperiment, ProbComp.eval_bind]
    trans (ProbComp.eval Com.keyGen).bind fun _ => PMF.pure false
    · refine pmfBind_congr _ fun ck => ?_
      rw [eval_unlinkOracleProgram_mkSig_issue Com nfGen tag S bound sys adv pk ctx 2 2 mkSig
        (by omega) (by omega) hmksig (fun _ => rfl) (fun _ _ _ _ _ => rfl) true b ck]
      have hstep : ∀ nf0 r0 nf1 r1,
          ProbComp.eval ((preLoopOracle Com nfGen tag S bound adv ck pk ctx true b 2
            (by omega)
            ⟨nf0, 2, r0, Com.eval ck ⟨nf0, ctx, 2⟩ r0, 0,
              mkSig (tag (Com.eval ck ⟨nf0, ctx, 2⟩ r0) 0)⟩
            ⟨nf1, 2, r1, Com.eval ck ⟨nf1, ctx, 2⟩ r1, 0,
              mkSig (tag (Com.eval ck ⟨nf1, ctx, 2⟩ r1) 0)⟩ ()).run
            (realProofOracle Com tag S bound sys ck)) = PMF.pure false := by
        intro nf0 r0 nf1 r1
        rw [eval_refund_preLoopOracle Com nfGen tag S bound sys hbound pk ctx mkSig hmksig ck true b
          nf0 nf1 r0 r1]
        have hchal : ∀ nf0' r0' nf1' r1',
            ProbComp.eval ((preLoopOracle Com nfGen tag S bound adv ck pk ctx true b 0
              (by omega)
              ⟨nf0', 1, r0', Com.eval ck ⟨nf0', ctx, 1⟩ r0', 2,
                mkSig (tag (Com.eval ck ⟨nf0', ctx, 1⟩ r0') 2)⟩
              ⟨nf1', 1, r1', Com.eval ck ⟨nf1', ctx, 1⟩ r1', 0,
                mkSig (tag (Com.eval ck ⟨nf1', ctx, 1⟩ r1') 0)⟩ ()).run
              (realProofOracle Com tag S bound sys ck)) = PMF.pure false := by
          intro nf0' r0' nf1' r1'
          cases b
          · simp only [preLoopOracle, Bool.false_eq_true, ↓reduceIte]
            exact eval_challengeLoop_debit2_false Com nfGen tag S bound sys adv (fun _ => rfl) ck pk
              ctx true _ 1 0 (Or.inr ⟨rfl, by simp⟩)
          · simp only [preLoopOracle, ↓reduceIte]
            exact eval_challengeLoop_debit2_false Com nfGen tag S bound sys adv (fun _ => rfl) ck pk
              ctx true _ 1 2 (Or.inl (by simp))
        dsimp only [adv] at hchal
        simp only [hchal, PMF.bind_const]
      simp only [hstep, PMF.bind_const]
    · simp only [PMF.bind_const]
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

/-- Explicit multi-instance ZK distinguisher for the adaptive unlinkability reduction: draws a
uniform challenge bit `b ← Bool`, runs `unlinkOracleProgram` on `b`, and tests whether the
adversary's output equals `b` (giving the factor of `2` via
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
structure SimEnv
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
def challengeLoopSim {preRounds challengeSpends : ℕ}
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
def preLoopSim {preRounds challengeSpends : ℕ}
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
    simp only [preLoopSim]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact challengeLoopSim_cutoff_congr env adv pk ctx hop1 hop2 challengeSpends
        (le_refl _) (by omega) (by omega) _ _ _ _
    · simp only [↓reduceIte]
      exact challengeLoopSim_cutoff_congr env adv pk ctx hop1 hop2 challengeSpends
        (le_refl _) (by omega) (by omega) _ _ _ _
  | succ rem' ih =>
    have hf1 : ¬ (2 + (preRounds - (rem' + 1)) < hop1) := by omega
    have hf2 : ¬ (2 + (preRounds - (rem' + 1)) < hop2) := by omega
    simp only [preLoopSim, hf1, hf2, ↓reduceIte]
    congr 1 with choice
    by_cases hguard : spendAdmissible env.bound
        (if choice.client then note1 else note0).bal
        (if choice.client then note1 else note0).ref choice.debit = false
    · simp only [hguard, Bool.not_false, ↓reduceIte]
    · have hguardT := Bool.eq_true_of_not_eq_false hguard
      simp only [hguardT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
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
  by_cases hfin : (c1 && c2) = false
  · simp only [hfin, Bool.not_false, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure]
  · have hfinAnd := Bool.eq_true_of_not_eq_false hfin
    simp only [hfinAnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hc := Bool.and_eq_true _ _ |>.mp hfinAnd
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
    by_cases hguard : (spendAdmissible env.bound noteAct.bal noteAct.ref choice.debit &&
        spendAdmissible env.bound balOther refOther choice.debit) = false
    · simp only [hguard, Bool.not_false, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure]
    · have hguardT := Bool.eq_true_of_not_eq_false hguard
      simp only [hguardT, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_bind,
        ProbOracleComp.run_sample, ProbOracleComp.run_query, ProbComp.eval_bind]
      have hokAct : spendAdmissible env.bound noteAct.bal noteAct.ref choice.debit = true :=
        (Bool.and_eq_true _ _ |>.mp hguardT).1
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
    simp only [preLoopOracle, preLoopSim]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact challengeLoopOracle_sim_eq env adv pk ctx challengeSpends (le_refl _)
        note0 note1.bal note1.ref st h0
    · simp only [↓reduceIte]
      exact challengeLoopOracle_sim_eq env adv pk ctx challengeSpends (le_refl _)
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
  by_cases hinit : (decide (0 < initOut.t0) && decide (initOut.t0 < env.bound) &&
      decide (0 < initOut.t1) && decide (initOut.t1 < env.bound)) = false
  · simp only [hinit, Bool.not_false, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure]
  · have hinitAnd := Bool.eq_true_of_not_eq_false hinit
    simp only [hinitAnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_bind,
      ProbOracleComp.run_sample, ProbOracleComp.run_query, ProbComp.eval_bind]
    obtain ⟨ht0pos, ht0ub, ht1pos, ht1ub⟩ := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hinitAnd
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
    by_cases hiss : (env.S.verify initOut.pk (env.tag
        (env.Com.eval env.ck ⟨nf0, initOut.ctx, initOut.t0⟩ r0) 0) issResp.s0 &&
        env.S.verify initOut.pk (env.tag
        (env.Com.eval env.ck ⟨nf1, initOut.ctx, initOut.t1⟩ r1) 0) issResp.s1) = false
    · simp only [hiss, Bool.not_false, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure]
    · have hissAnd := Bool.eq_true_of_not_eq_false hiss
      simp only [hissAnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hsigs :
          env.S.verify initOut.pk (env.tag (env.Com.eval env.ck ⟨nf0, initOut.ctx, initOut.t0⟩ r0)
            0) issResp.s0 = true ∧
          env.S.verify initOut.pk (env.tag (env.Com.eval env.ck ⟨nf1, initOut.ctx, initOut.t1⟩ r1)
            0) issResp.s1 = true := by
        simpa only [Bool.and_eq_true] using hissAnd
      exact preLoopOracle_sim_eq env adv initOut.pk initOut.ctx b preRounds (le_refl _)
        ⟨nf0, initOut.t0, r0, env.Com.eval env.ck ⟨nf0, initOut.ctx, initOut.t0⟩ r0, 0, issResp.s0⟩
        ⟨nf1, initOut.t1, r1, env.Com.eval env.ck ⟨nf1, initOut.ctx, initOut.t1⟩ r1, 0, issResp.s1⟩
        issResp.st
        ⟨rfl, ht0ub, show (0 : ℕ) < env.bound by omega, hsigs.1⟩
        ⟨rfl, ht1ub, show (0 : ℕ) < env.bound by omega, hsigs.2⟩

/-- Challenge pause step: stops right before commitment slot `idx` equals `pauseSlot`. -/
def challengeLoopPause {preRounds challengeSpends : ℕ}
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
def preLoopPause {preRounds challengeSpends : ℕ}
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
def runPause {preRounds challengeSpends : ℕ}
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
def resumeAfterCom {preRounds challengeSpends : ℕ}
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
    by_cases hguard : (spendAdmissible env.bound noteAct.bal noteAct.ref choice.debit &&
        spendAdmissible env.bound balOther refOther choice.debit) = false
    · simp only [hguard, Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
        PMF.pure_bind, PMF.bind_const]
    · have hguardT := Bool.eq_true_of_not_eq_false hguard
      simp only [hguardT, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind,
        PMF.bind_bind]
      refine pmfBind_congr _ fun nfPrime => ?_
      by_cases heq : 2 + preRounds + (challengeSpends - (rem' + 1)) = pauseSlot
      · have hrem_eq : challengeSpends - (challengeSpends - (rem' + 1) + 1) = rem' := by omega
        cases isDummy
        · have hltF : ¬ (2 + preRounds + (challengeSpends - (rem' + 1)) < pauseSlot) := by omega
          simp only [heq, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
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
        by_cases hfin : (decide (resp.refund < env.bound) &&
            env.S.verify pk (env.tag (env.Com.eval env.ck
              ⟨env.dummyNf, ctx, 0⟩ rPrime) resp.refund) resp.sig) = false
        · simp only [hfin, Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
            PMF.pure_bind, PMF.bind_const]
        · have hfinT := Bool.eq_true_of_not_eq_false hfin
          simp only [hfinT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hih := ih (by omega) (by omega)
            ⟨nfPrime, noteAct.bal + noteAct.ref - choice.debit, resp.refund⟩
            (balOther + refOther - choice.debit) resp.refund resp.st
          simp only [ProbComp.eval_bind] at hih
          exact hih

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
    simp only [preLoopPause, preLoopSim]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact challengeLoopPause_resume_eq env adv pk ctx isDummy pauseSlot challengeSpends
        (le_refl _) (by omega) note0 note1.bal note1.ref st
    · simp only [↓reduceIte]
      exact challengeLoopPause_resume_eq env adv pk ctx isDummy pauseSlot challengeSpends
        (le_refl _) (by omega) note1 note0.bal note0.ref st
  | succ rem' ih =>
    simp only [preLoopPause, preLoopSim, ProbComp.eval_bind, PMF.bind_bind]
    refine pmfBind_congr _ fun choice => ?_
    set noteSel := if choice.client then note1 else note0
    by_cases hguard : spendAdmissible env.bound noteSel.bal noteSel.ref choice.debit = false
    · simp only [hguard, Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
        PMF.pure_bind, PMF.bind_const]
    · have hguardT := Bool.eq_true_of_not_eq_false hguard
      simp only [hguardT, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind,
        PMF.bind_bind]
      refine pmfBind_congr _ fun nfPrime => ?_
      by_cases heq : 2 + (preRounds - (rem' + 1)) = pauseSlot
      · have hrem_eq : preRounds - (preRounds - (rem' + 1) + 1) = rem' := by omega
        cases isDummy
        · simp only [heq, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.pure_bind, resumeAfterCom, hrem_eq, Nat.lt_irrefl, noteSel]
          refine pmfBind_congr _ fun rPrime => pmfBind_congr _ fun pi =>
            pmfBind_congr _ fun resp => ?_
          by_cases hfin : (decide (resp.refund < env.bound) &&
              env.S.verify pk (env.tag (env.Com.eval env.ck
                ⟨nfPrime, ctx, (if choice.client then note1 else note0).bal +
                  (if choice.client then note1 else note0).ref - choice.debit⟩ rPrime)
                resp.refund) resp.sig) = false
          · simp only [hfin, Bool.not_false, ↓reduceIte]
          · have hfinT := Bool.eq_true_of_not_eq_false hfin
            simp only [hfinT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact congrArg ProbComp.eval (preLoopSim_cutoff_congr env adv pk ctx b (pauseSlot + 1)
              pauseSlot rem' (by omega) (by omega) (by omega) _ _ _)
        · simp only [heq, ↓reduceIte, Nat.lt_succ_self, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.pure_bind, resumeAfterCom, hrem_eq, noteSel]
      · have hlt : 2 + (preRounds - (rem' + 1)) < pauseSlot := by omega
        have hlt' : 2 + (preRounds - (rem' + 1)) <
            (if isDummy then pauseSlot + 1 else pauseSlot) := by
          cases isDummy <;> simp <;> omega
        simp only [heq, ↓reduceIte, hlt, hlt', ProbComp.eval_bind, PMF.bind_bind]
        refine pmfBind_congr _ fun rPrime => pmfBind_congr _ fun pi =>
          pmfBind_congr _ fun resp => ?_
        by_cases hfin : (decide (resp.refund < env.bound) &&
            env.S.verify pk (env.tag (env.Com.eval env.ck
              ⟨env.dummyNf, ctx, 0⟩ rPrime) resp.refund) resp.sig) = false
        · simp only [hfin, Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
            PMF.pure_bind, PMF.bind_const]
        · have hfinT := Bool.eq_true_of_not_eq_false hfin
          simp only [hfinT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hih := ih (by omega) (by omega)
            (if choice.client then note0
              else ⟨nfPrime, noteSel.bal + noteSel.ref - choice.debit, resp.refund⟩)
            (if choice.client
              then ⟨nfPrime, noteSel.bal + noteSel.ref - choice.debit, resp.refund⟩
              else note1)
            resp.st
          simp only [ProbComp.eval_bind] at hih
          exact hih

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
  by_cases hinit : (decide (0 < initOut.t0) && decide (initOut.t0 < env.bound) &&
      decide (0 < initOut.t1) && decide (initOut.t1 < env.bound)) = false
  · simp only [hinit, Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
      PMF.pure_bind, PMF.bind_const]
  · have hinitT := Bool.eq_true_of_not_eq_false hinit
    simp only [hinitT, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind,
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
        by_cases hfin : (env.S.verify initOut.pk (env.tag (env.Com.eval env.ck
              ⟨env.dummyNf, initOut.ctx, 0⟩ r0) 0) issResp.s0 &&
            env.S.verify initOut.pk (env.tag (env.Com.eval env.ck
              ⟨env.dummyNf, initOut.ctx, 0⟩ r1) 0) issResp.s1) = false
        · simp only [hfin, Bool.not_false, ↓reduceIte, resumeAfterCom, ProbComp.eval_pure,
            PMF.pure_bind, PMF.bind_const]
        · have hfinT := Bool.eq_true_of_not_eq_false hfin
          simp only [hfinT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hsub := preLoopPause_resume_eq env adv initOut.pk initOut.ctx b isDummy pauseSlot
            preRounds (le_refl _) (by omega) ⟨nf0, initOut.t0, 0⟩ ⟨nf1, initOut.t1, 0⟩
            issResp.st
          simp only [ProbComp.eval_bind] at hsub
          exact hsub

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
  /-- Sampled challenge bit `b`. -/
  b : Bool
  /-- Sampled commitment hybrid slot `hop`. -/
  hop : Fin (2 + preRounds + challengeSpends)
  /-- Continuation frozen immediately before commitment slot `hop`. -/
  cont : SimContinuation PK Context C Nullifier Proof State preRounds challengeSpends

/-- Deterministic witness value extracted from the nonempty support of `nfGen`. -/
noncomputable def defaultNf {Nullifier : Type} (nfGen : ProbComp Nullifier) : Nullifier :=
  Classical.choose (ProbComp.eval nfGen).support_nonempty

/-- Commutes two independent leading `PMF.bind` draws past a third `PMF.bind`. -/
private lemma pmfBind_comm2 {α β γ δ : Type} (p : PMF α) (q : PMF β) (r : PMF γ)
    (k : α → β → γ → PMF δ) :
    (p.bind fun a => q.bind fun b => r.bind fun c => k a b c) =
      r.bind fun c => p.bind fun a => q.bind fun b => k a b c := by
  conv_lhs => enter [2, a]; rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- Explicit `TwoStage` commitment-hiding reduction for the adaptive unlinkability reduction:
samples uniform challenge bit `b ← Bool` and random commitment hybrid slot
`hop ← Fin (2 + preRounds + challengeSpends)`, runs the simulator up to `hop`, submits
`(msgReal, msgDummy)` to `Com.toScheme`, and tests whether the resumed adversary guesses `b`. -/
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
    let b ← ProbComp.uniform Bool
    let hop ← ProbComp.uniform (Fin (2 + preRounds + challengeSpends))
    let env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof :=
      ⟨Com, nfGen, tag, S, bound, sys, ck, defaultNf nfGen⟩
    let res ← runPause env adv b hop.val
    return (⟨res.msgReal, res.msgDummy⟩, ⟨ck, b, hop, res.cont⟩)
  guess st cStar := do
    let env : SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof :=
      ⟨Com, nfGen, tag, S, bound, sys, st.ck, defaultNf nfGen⟩
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
      by_cases hguard : spendAdmissible env.bound bal0 ref0 choice.debit = false
      · simp only [hguard, Bool.not_false, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]
      · have hguardT := Bool.eq_true_of_not_eq_false hguard
        simp only [hguardT, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind]
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
      by_cases hguard : spendAdmissible env.bound bal1 ref1 choice.debit = false
      · simp only [hguard, Bool.not_false, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]
      · have hguardT := Bool.eq_true_of_not_eq_false hguard
        simp only [hguardT, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind]
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

/-- **Adaptive malicious-issuer unlinkability reduction** (original finite query-bounded
formalization for `[VOLEACT2026]`, `#issuance` and `#spending`):
for any adaptive adversary `adv` against `unlinkabilityExperiment`,
`Adv^unlink ≤ 2 * Adv^ZK + 2 * (2 + preRounds + challengeSpends) * Adv^hide`
via `zkDistinguisher` and `unlinkHidingReduction`.
When `preRounds = 0`, the hiding factor specializes directly to `2 * (2 + challengeSpends)`.
The leading factor of `2` converts the `[0, 1]` two-world `Game.advantage` into `[0, 1/2]`
bit-guessing bias via the `b ← ProbComp.uniform Bool` XOR wrapper
(`Game.advantage_le_two_mul_uniform_bool_xor`),
and replacing all `2 + preRounds + challengeSpends` emitted commitments sequentially avoids
guessing which pre-challenge spend terminates each client's branch under adaptive `choosePre`. -/
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
  let envOf : CommitKey → SimEnv CommitKey PK C Context Nullifier O Sig Target SK Proof :=
    fun ck => ⟨Com, nfGen, tag, S, bound, sys, ck, defaultNf nfGen⟩
  let g0Fn : CommitKey → Bool → ProbComp Bool := fun ck b =>
    (unlinkOracleProgram Com nfGen tag S bound adv true b ck).run
      (realProofOracle Com tag S bound sys ck)
  let g1Fn : CommitKey → Bool → ProbComp Bool := fun ck b =>
    runSimProgram (envOf ck) adv b 0
  let hybFn : ℕ → Game := fun h => bitGame (fun ck b => runSimProgram (envOf ck) adv b h)
  have hbit_eq (fn : CommitKey → Bool → ProbComp Bool) :
      (bitGame fn true).toReal =
        (1 / 2 : ℝ) + (1 / 2 : ℝ) *
          ((ProbComp.eval (Com.keyGen >>= fun ck => fn ck true) true).toReal -
            (ProbComp.eval (Com.keyGen >>= fun ck => fn ck false) true).toReal) := by
    let P : Game := ProbComp.eval (Com.keyGen >>= fun ck => fn ck false)
    let Q : Game := ProbComp.eval (Com.keyGen >>= fun ck => fn ck true)
    have hcomm : bitGame fn =
        (uniformOfFintype Bool).bind fun b =>
          (if b then Q else P).bind fun g => PMF.pure (decide (g = b)) := by
      simp only [bitGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
      rw [PMF.bind_comm]
      refine pmfBind_congr _ fun b => ?_
      cases b <;>
        simp only [P, Q, ProbComp.eval_bind, PMF.bind_bind, Bool.false_eq_true, ↓reduceIte]
    have hval : bitGame fn true = (2 : ℝ≥0∞)⁻¹ * (Q true + P false) := by
      rw [hcomm, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
      simp only [uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ↓reduceIte,
        Bool.false_eq_true]
      have hf : (P.bind fun g => PMF.pure (decide (g = false))) true = P false := by
        rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
        simp
      have ht : (Q.bind fun g => PMF.pure (decide (g = true))) true = Q true := by
        rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
        simp
      rw [ht, hf, mul_add]
    have hPsum : P false + P true = 1 := by
      have hs := P.tsum_coe
      rw [tsum_fintype, Fintype.sum_bool, add_comm] at hs
      exact hs
    have hPtoReal : (P false).toReal = 1 - (P true).toReal := by
      have := congrArg ENNReal.toReal hPsum
      rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
        ENNReal.toReal_one] at this
      linarith
    rw [hval, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), hPtoReal]
    ring
  have hzkReal : multiProofZKRealGame Com tag S bound sys
      (zkDistinguisher Com nfGen tag S bound adv) = bitGame g0Fn := by
    simp only [multiProofZKRealGame, zkDistinguisher, bitGame, g0Fn, ProbOracleComp.run_bind,
      ProbOracleComp.run_sample, ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure]
  have hzkSim : multiProofZKSimGame Com tag S bound sys
      (zkDistinguisher Com nfGen tag S bound adv) = bitGame g1Fn := by
    simp only [multiProofZKSimGame, zkDistinguisher, bitGame, g1Fn, ProbOracleComp.run_bind,
      ProbOracleComp.run_sample, ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure]
    refine pmfBind_congr _ fun ck => pmfBind_congr _ fun b => ?_
    rw [unlinkOracleProgram_sim_eq (envOf ck) adv b]
  have hhyb0 : hybFn 0 = bitGame g1Fn := rfl
  have hhybN_val : (hybFn N true).toReal = 1 / 2 := by
    have heq : ProbComp.eval (Com.keyGen >>= fun ck => runSimProgram (envOf ck) adv true N) =
        ProbComp.eval (Com.keyGen >>= fun ck => runSimProgram (envOf ck) adv false N) := by
      simp only [ProbComp.eval_bind]
      refine pmfBind_congr _ fun ck => (g4_false_eq_true (envOf ck) adv).symm
    rw [hbit_eq, heq, sub_self, mul_zero, add_zero]
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
    have hsw : ∀ ck : CommitKey,
        ((uniformOfFintype Bool).bind fun b =>
          (uniformOfFintype (Fin N)).bind fun h =>
            (ProbComp.eval (runPause (envOf ck) adv b h.val)).bind fun res =>
              (ProbComp.eval Com.openSample).bind fun r =>
                (ProbComp.eval (resumeAfterCom (envOf ck) adv h.val res.cont
                  (Com.eval ck (MessagePair.select ⟨res.msgReal, res.msgDummy⟩ bHide) r))).bind
                  fun g => PMF.pure (decide (g = b))) =
        ((uniformOfFintype (Fin N)).bind fun h =>
          (uniformOfFintype Bool).bind fun b =>
            (ProbComp.eval (runSimProgram (envOf ck) adv b
              (if bHide then h.val + 1 else h.val))).bind fun g => PMF.pure (decide (g = b))) := by
      intro ck
      rw [PMF.bind_comm]
      refine pmfBind_congr _ fun h => pmfBind_congr _ fun b => ?_
      cases bHide
      · simp only [MessagePair.select_false, Bool.false_eq_true, ↓reduceIte]
        have hreal := runPause_real_eq (envOf ck) adv b h.val
        calc _ = ((ProbComp.eval (do
                let res ← runPause (envOf ck) adv b h.val
                let r ← Com.openSample
                resumeAfterCom (envOf ck) adv h.val res.cont
                  (Com.eval ck res.msgReal r))).bind fun g => PMF.pure (decide (g = b))) := by
              simp only [ProbComp.eval_bind, PMF.bind_bind]
          _ = _ := by rw [hreal]
      · simp only [MessagePair.select_true, ↓reduceIte]
        have hdummy := runPause_dummy_eq (envOf ck) adv b h.val
        calc _ = ((ProbComp.eval (do
                let res ← runPause (envOf ck) adv b h.val
                let r ← Com.openSample
                resumeAfterCom (envOf ck) adv h.val res.cont
                  (Com.eval ck res.msgDummy r))).bind fun g => PMF.pure (decide (g = b))) := by
              simp only [ProbComp.eval_bind, PMF.bind_bind]
          _ = _ := by rw [hdummy]
    conv_rhs => rw [PMF.bind_comm]
    exact pmfBind_congr _ fun ck => hsw ck
  have hhideFalse :
      ProbComp.eval (Com.toScheme.hidingExperiment
        (unlinkHidingReduction Com nfGen tag S bound sys adv) false) =
        (uniformOfFintype (Fin N)).bind (fun h : Fin N => hybFn h.val) := by
    simpa only [Bool.false_eq_true, ↓reduceIte] using hhide_eq false
  have hhideTrue :
      ProbComp.eval (Com.toScheme.hidingExperiment
        (unlinkHidingReduction Com nfGen tag S bound sys adv) true) =
        (uniformOfFintype (Fin N)).bind (fun h : Fin N => hybFn (h.val + 1)) := by
    simpa only [↓reduceIte] using hhide_eq true
  have htel :
      (N : ℝ) * ((ProbComp.eval (Com.toScheme.hidingExperiment
          (unlinkHidingReduction Com nfGen tag S bound sys adv) false) true).toReal -
        (ProbComp.eval (Com.toScheme.hidingExperiment
          (unlinkHidingReduction Com nfGen tag S bound sys adv) true) true).toReal) =
      (hybFn 0 true).toReal - (hybFn N true).toReal := by
    rw [hhideFalse, hhideTrue, PMF.bind_apply, PMF.bind_apply, tsum_fintype, tsum_fintype]
    simp only [uniformOfFintype_apply, Fintype.card_fin]
    have hNpos : (0 : ℝ) < N := by positivity
    have hNne : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
    have htoRealSum (f : ℕ → Game) :
        (∑ i : Fin N, ((N : ℝ≥0∞)⁻¹ * f i.val true)).toReal =
        (N : ℝ)⁻¹ * ∑ i : Fin N, (f i.val true).toReal := by
      rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top
        (ENNReal.inv_ne_top.mpr (by positivity)) (PMF.apply_ne_top _ _))]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← Finset.mul_sum]
    have h1 := htoRealSum hybFn
    have h2 := htoRealSum (fun k => hybFn (k + 1))
    rw [h1, h2]
    have hfinSum (m : ℕ) :
        ∑ i : Fin m, ((hybFn i.val true).toReal - (hybFn (i.val + 1) true).toReal) =
          (hybFn 0 true).toReal - (hybFn m true).toReal := by
      induction m with
      | zero => simp
      | succ k ih =>
        rw [Fin.sum_univ_castSucc, Fin.val_last]
        simp only [Fin.val_castSucc]
        rw [ih]
        ring
    rw [← mul_sub, ← Finset.sum_sub_distrib, hfinSum N]
    field_simp
  have hhybAbs :
      |(hybFn 0 true).toReal - (hybFn N true).toReal| =
        (N : ℝ) * (Experiment.advantage
          (Com.toScheme.hidingExperiment
            (unlinkHidingReduction Com nfGen tag S bound sys adv) false)
          (Com.toScheme.hidingExperiment
            (unlinkHidingReduction Com nfGen tag S bound sys adv) true) : ℝ) := by
    rw [← htel, abs_mul, abs_of_nonneg (Nat.cast_nonneg N), Experiment.coe_advantage]
  have hunlink_eq :
      (Game.advantage
        (unlinkabilityExperiment Com nfGen tag S bound sys adv false)
        (unlinkabilityExperiment Com nfGen tag S bound sys adv true) : ℝ) =
      2 * |(bitGame g0Fn true).toReal - (hybFn N true).toReal| := by
    rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability]
    have hg0false : unlinkabilityExperiment Com nfGen tag S bound sys adv false =
        ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck false) := rfl
    have hg0true : unlinkabilityExperiment Com nfGen tag S bound sys adv true =
        ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck true) := rfl
    rw [hg0false, hg0true, hbit_eq g0Fn, hhybN_val]
    have ha :
        |((1 / 2 : ℝ) + (1 / 2 : ℝ) *
            ((ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck true) true).toReal -
              (ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck false) true).toReal)) -
            (1 / 2 : ℝ)| =
        (1 / 2 : ℝ) *
          |(ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck false) true).toReal -
            (ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck true) true).toReal| := by
      have : ((1 / 2 : ℝ) + (1 / 2 : ℝ) *
            ((ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck true) true).toReal -
              (ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck false) true).toReal)) -
            (1 / 2 : ℝ) =
          -(1 / 2 : ℝ) *
            ((ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck false) true).toReal -
              (ProbComp.eval (Com.keyGen >>= fun ck => g0Fn ck true) true).toReal) := by ring
      rw [this, abs_mul, abs_neg, abs_of_nonneg (by norm_num)]
    rw [ha]
    ring
  rw [hunlink_eq, hzkReal, hzkSim]
  have htri :
      |(bitGame g0Fn true).toReal - (hybFn N true).toReal| ≤
        |(bitGame g0Fn true).toReal - (bitGame g1Fn true).toReal| +
        |(hybFn 0 true).toReal - (hybFn N true).toReal| := by
    rw [hhyb0]
    exact abs_sub_le _ _ _
  calc 2 * |(bitGame g0Fn true).toReal - (hybFn N true).toReal|
      ≤ 2 * (|(bitGame g0Fn true).toReal - (bitGame g1Fn true).toReal| +
          |(hybFn 0 true).toReal - (hybFn N true).toReal|) := by linarith
    _ = 2 * (Game.advantage (bitGame g0Fn) (bitGame g1Fn) : ℝ) +
          2 * (N : ℝ) * (Experiment.advantage
            (Com.toScheme.hidingExperiment
              (unlinkHidingReduction Com nfGen tag S bound sys adv) false)
            (Com.toScheme.hidingExperiment
              (unlinkHidingReduction Com nfGen tag S bound sys adv) true) : ℝ) := by
      rw [hhybAbs, Game.coe_advantage (bitGame g0Fn) (bitGame g1Fn), Game.coe_succProbability,
        Game.coe_succProbability]
      ring

end UnlinkabilityReductionContinuation

section CRTDecoupling

open CRTHazard

/-- Transcript token bundle exposed to an `H5`-querying distinguisher in the CRT witness-reuse
model (`G8` coupled vs `G8.5` decoupled). -/
structure CRTProofToken (C IV : Type) (nMult lam nMask : ℕ) where
  /-- Note commitment `c = Com.eval ck m r`. -/
  com : C
  /-- Per-proof initialization vector `iv`. -/
  iv : IV
  /-- Verifier mask delta `d`. -/
  d : Fin lam → ZMod 2
  /-- Garbled gate multiplier table `cmult`. -/
  cmult : Fin nMult → Fin nMask → ZMod 2

/-- Configuration for non-black-box CRT witness-reuse decoupling (`G8 → G8.5`, where `G8` follows
[BaumEtAl2026FAEST] §10.10 Theorem 10.42 and `G8.5` is this library's intermediate hop): `qTok`
token events (`0 < qTok`) with non-adaptive `ck`-fixed messages, openings `r j` in `r`-first
layout (`Fin lam → ZMod 2`), IV generator `ivGen`, gate labels `baseLabel`, and `adv` making
adaptive `H5` queries over all `qTok` token bundles delivered together. -/
structure G85Setup
    (CommitKey C Nullifier Context IV : Type) (nMult lam nMask qTok : ℕ) where
  /-- Deterministic-evaluation opening commitment with openings in `Fin lam → ZMod 2`. -/
  Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C (Fin lam → ZMod 2)
  /-- Non-adaptive real note message per token event `j : Fin qTok`, fixed by `ck`. -/
  msgs : CommitKey → Fin qTok → CommitMsg Nullifier Context
  /-- Per-token IV distribution. -/
  ivGen : CommitKey → Fin qTok → ProbComp IV
  /-- Base garbled-circuit wire labels `(j, e) ↦ L₀(j, e)`. -/
  baseLabel : CommitKey → Fin qTok → Fin nMult → Fin lam → ZMod 2
  /-- `H5`-adaptive distinguisher receiving all `qTok` token bundles together. -/
  adv : CommitKey → (Fin qTok → CRTProofToken C IV nMult lam nMask) →
    ProbOracleComp (H5Spec IV nMult lam nMask) Bool

variable {CommitKey C Nullifier Context IV : Type} {nMult lam nMask qTok : ℕ}
variable [DecidableEq IV]

/-- Sample a tuple over `Fin n` from independent component distributions. -/
def samplePi : (n : ℕ) → {α : Type} → (Fin n → ProbComp α) → ProbComp (Fin n → α)
  | 0, _, _ => pure Fin.elim0
  | n + 1, _, f => do
    let x ← f 0
    let rest ← samplePi n (fun i => f i.succ)
    return Fin.cases x rest

/-- Replacing component `j` of `samplePi` with an independent draw `y ← f j` preserves the
product distribution. -/
private lemma samplePi_replace {n : ℕ} {α : Type}
    (f : Fin n → ProbComp α) (default : Fin n → α) (j : Fin n) :
    ((ProbComp.eval (samplePi n (fun i => if i = j then pure (default i) else f i))).bind
      fun rest => (ProbComp.eval (f j)).map fun y => Function.update rest j y) =
      ProbComp.eval (samplePi n f) := by
  induction n generalizing α with
  | zero => exact Fin.elim0 j
  | succ n' ih =>
    refine Fin.cases ?_ ?_ j
    · have hsub :
          (fun i : Fin n' =>
            if i.succ = (0 : Fin (n' + 1)) then pure (default i.succ) else f i.succ) =
          fun i => f i.succ :=
        funext fun i => ite_eq_right_iff.mpr fun h => absurd h (Fin.succ_ne_zero i)
      simp only [samplePi, ↓reduceIte, hsub, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def]
      rw [PMF.bind_comm]
      refine pmfBind_congr _ fun x => pmfBind_congr _ fun rest => congrArg PMF.pure ?_
      funext i
      exact Fin.cases rfl (fun k => by simp [Function.update, Fin.succ_ne_zero]) i
    · intro j'
      have hsub :
          (fun i : Fin n' =>
            if i.succ = j'.succ then pure (default i.succ) else f i.succ) =
          fun i => if i = j' then pure (default i.succ) else f i.succ :=
        funext fun i => by simp [Fin.succ_inj]
      have hne : (0 : Fin (n' + 1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
      simp only [samplePi, hne, ↓reduceIte, hsub, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.bind_bind, PMF.pure_bind]
      refine pmfBind_congr _ fun x0 => ?_
      rw [← ih (fun i => f i.succ) (fun i => default i.succ) j']
      simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
      refine pmfBind_congr _ fun rest => pmfBind_congr _ fun y => congrArg PMF.pure ?_
      funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [Function.update, (Fin.succ_ne_zero j').symm]
      · by_cases hk : k = j'
        · subst k; simp [Function.update]
        · simp [Function.update, hk, Fin.succ_inj]

/-- Complementary `H5` query key `(iv j, e, baseLabel ck j e + d j + r j)` for token `j` and
gate `e`. -/
def badH5Key (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (j : Fin qTok) (e : Fin nMult) : H5Query IV nMult lam :=
  ⟨iv j, e, setup.baseLabel ck j e + d j + r j⟩

/-- Boolean check testing whether an `H5` query hits `badH5Key` for some token `j` and gate `e`. -/
def isBadH5Query (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (q : H5Query IV nMult lam) : Bool :=
  decide (∃ j : Fin qTok, ∃ e : Fin nMult, q = badH5Key setup ck iv d r j e)

/-- Coupled `G8` game ([BaumEtAl2026FAEST] §10.10, Theorem 10.42) under the witness-reuse CRT mask
option reusing commitment opening `r j` (`r`-first layout, rather than a flag named in
[BaumEtAl2026FAEST] or [VOLEACT2026]): draws `u j`, sets `d j := r j + u j`, and sets `cmult j e`
directly to the raw `H5` value at `badH5Key`. -/
noncomputable def g8Game [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok) : Game :=
  ProbComp.eval do
    let ck ← setup.Com.keyGen
    let h5 ← ProbComp.uniform (H5Query IV nMult lam → Fin nMask → ZMod 2)
    let r ← samplePi qTok (fun _ => setup.Com.openSample)
    let u ← ProbComp.uniform (Fin qTok → Fin lam → ZMod 2)
    let iv ← samplePi qTok (setup.ivGen ck)
    let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
      let d := r j + u j
      let cmult : Fin nMult → Fin nMask → ZMod 2 :=
        fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + u j⟩
      ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d, cmult⟩
    (setup.adv ck tok).run (fun q => pure (h5 q))

/-- Coupled `G8` `StateT Bool` oracle returning `cmult` on `badH5Key` and `h5` otherwise. -/
noncomputable def g8Handler
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (cmult : Fin qTok → Fin nMult → Fin nMask → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) (bad : Bool) : PMF ((Fin nMask → ZMod 2) × Bool) := by
  classical
  exact if h : ∃ p : Fin qTok × Fin nMult, q = badH5Key setup ck iv d r p.1 p.2 then
    pure (cmult (Classical.choose h).1 (Classical.choose h).2, true)
  else
    pure (h5 q, bad)

/-- Decoupled `G8.5` (this library's intermediate hop between FAEST's `G8` and `G9`) `StateT Bool`
oracle returning `h5 q` uniformly while latching `bad := true` if `isBadH5Query` triggers. -/
noncomputable def g85Handler
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) (bad : Bool) : PMF ((Fin nMask → ZMod 2) × Bool) :=
  pure (h5 q, bad || isBadH5Query setup ck iv d r q)

/-- `ProbComp`-valued variant of `g85Handler` for `ProbOracleComp.runState`. -/
def g85HandlerP (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) : StateT Bool ProbComp (Fin nMask → ZMod 2) :=
  fun bad => pure (h5 q, bad || isBadH5Query setup ck iv d r q)

/-- Full decoupled `G8.5` (library intermediate hop) joint execution over
`(output, badH5, ivCollision)`. -/
noncomputable def g85FullRun [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok) :
    ProbComp (Bool × Bool × Bool) := do
  let ck ← setup.Com.keyGen
  let h5 ← ProbComp.uniform (H5Query IV nMult lam → Fin nMask → ZMod 2)
  let r ← samplePi qTok (fun _ => setup.Com.openSample)
  let d ← ProbComp.uniform (Fin qTok → Fin lam → ZMod 2)
  let iv ← samplePi qTok (setup.ivGen ck)
  let cmult ← ProbComp.uniform (Fin qTok → Fin nMult → Fin nMask → ZMod 2)
  let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
    ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
  let res ← ((setup.adv ck tok).runState (g85HandlerP setup ck iv d r h5)).run false
  let ivColl : Bool := decide (¬ Function.Injective iv)
  return (res.1, res.2, ivColl)

/-- Decoupled `G8.5` (library intermediate hop) distinguishing game: `d j` and `cmult j` are
uniform and independent of `r j` and `h5`. -/
noncomputable def g85Game [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok) : Game :=
  (ProbComp.eval (g85FullRun setup)).map fun (out, _, _) => out

/-- Probability `Pr[¬ Function.Injective iv]` of an IV collision across the `qTok` proofs in
`g85FullRun` (`0` for counter IVs; replaces a fixed `2 ^ (-λ)` constant bound). -/
noncomputable def g85IvCollisionProb [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok) : ℝ :=
  (((ProbComp.eval (g85FullRun setup)).map fun (_, _, ivColl) => ivColl) true).toReal

/-- `IdenticalUntilBad` connecting `g8Handler` and `g85Handler` lifted to `ProbOracleComp`:
both agree identically while `bad = false` and preserve `bad = true` once triggered. -/
theorem crtDecouple_identicalUntilBad
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (cmult : Fin qTok → Fin nMult → Fin nMask → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) :
    OracleComp.IdenticalUntilBad
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (g8Handler setup ck iv d r cmult h5))
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (g85Handler setup ck iv d r h5))
      (fun bad : Bool => bad = true) where
  agree q s hs a s' hs' := by
    cases q with
    | inl n => rfl
    | inr q =>
      simp only [OracleComp.sumHandler, g8Handler, g85Handler, Bool.not_eq_true] at hs hs' ⊢
      by_cases hex : ∃ p : Fin qTok × Fin nMult, q = badH5Key setup ck iv d r p.1 p.2
      · have htrue : isBadH5Query setup ck iv d r q = true := by
          rcases hex with ⟨⟨j, e⟩, rfl⟩
          exact decide_eq_true ⟨j, e, rfl⟩
        simp [hex, htrue, hs, hs']
      · have hbadF : isBadH5Query setup ck iv d r q = false := by
          simp only [isBadH5Query, decide_eq_false_iff_not]
          rintro ⟨j, e, heq⟩
          exact hex ⟨(j, e), heq⟩
        simp [hex, hbadF, hs]
  absorb_first q s hs x hx := by
    cases q with
    | inl n =>
      obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact (Prod.mk.inj heq).2 ▸ hs
    | inr q =>
      simp only [OracleComp.sumHandler, g8Handler] at hx
      split_ifs at hx
      · change x ∈ (PMF.pure _).support at hx
        rw [PMF.mem_support_pure_iff] at hx
        rcases hx with rfl
        rfl
      · change x ∈ (PMF.pure _).support at hx
        rw [PMF.mem_support_pure_iff] at hx
        rcases hx with rfl
        exact hs
  absorb_second q s hs x hx := by
    cases q with
    | inl n =>
      obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact (Prod.mk.inj heq).2 ▸ hs
    | inr q =>
      simp only [OracleComp.sumHandler, g85Handler] at hx
      change x ∈ (PMF.pure _).support at hx
      rw [PMF.mem_support_pure_iff] at hx
      rcases hx with rfl
      simp only [hs, Bool.true_or]

/-- Query-logging `StateT` handler answering all `H5` queries from `h5` while recording queries. -/
noncomputable def h5LogHandler {IV : Type} {nMult lam nMask : ℕ}
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) (qs : List (H5Query IV nMult lam)) :
    PMF ((Fin nMask → ZMod 2) × List (H5Query IV nMult lam)) :=
  pure (h5 q, q :: qs)

/-- `ProbComp`-valued variant of `h5LogHandler` for `ProbOracleComp.runState`. -/
def h5LogHandlerP {IV : Type} {nMult lam nMask : ℕ}
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) :
    StateT (List (H5Query IV nMult lam)) ProbComp (Fin nMask → ZMod 2) :=
  fun qs => pure (h5 q, q :: qs)

/-- State passed across the two stages of `badH5HidingReduction`. -/
structure BadH5HidingState (CommitKey : Type) (qTok : ℕ) where
  /-- Commitment key `ck`. -/
  ck : CommitKey
  /-- Uniformly sampled target token index `j* : Fin qTok`. -/
  jStar : Fin qTok

/-- Shared `BadH5` log-running helper executing `setup.adv` with challenge commitment `cStar` at
target token index `jStar` and logging all `H5` queries. -/
noncomputable def runBadH5WithChallenge [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (jStar : Fin qTok) (cStar : C) :
    ProbComp (IV × (Fin lam → ZMod 2) × List (H5Query IV nMult lam)) := do
  let h5 ← ProbComp.uniform (H5Query IV nMult lam → Fin nMask → ZMod 2)
  let rOthers ← samplePi qTok (fun j => if j = jStar then pure 0 else setup.Com.openSample)
  let d ← ProbComp.uniform (Fin qTok → Fin lam → ZMod 2)
  let iv ← samplePi qTok (setup.ivGen ck)
  let cmult ← ProbComp.uniform (Fin qTok → Fin nMult → Fin nMask → ZMod 2)
  let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
    let c := if j = jStar then cStar else setup.Com.eval ck (setup.msgs ck j) (rOthers j)
    ⟨c, iv j, d j, cmult j⟩
  let res ← ((setup.adv ck tok).runState (h5LogHandlerP h5)).run []
  return (iv jStar, d jStar, res.2)

/-- Explicit `TwoStage` hiding reduction for `BadH5`: chooses a uniform target token `j*`,
submits `(msgs ck j*, (msgs ck j*).bumpBal)` (`bumpBal ≠ msgs ck j*`) to `Com.toScheme`, plugs
challenge `c*` into token `j*`, and tests whether any logged `H5` query recovers an opening `r*`
satisfying `Com.eval ck (msgs ck j*) r* = c*`. -/
noncomputable def badH5HidingReduction [DecidableEq C] [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    [NeZero qTok] :
    TwoStage CommitKey (MessagePair (CommitMsg Nullifier Context)) C Bool
      (BadH5HidingState CommitKey qTok) where
  choose ck := do
    let jStar ← ProbComp.uniform (Fin qTok)
    let m0 := setup.msgs ck jStar
    return (⟨m0, m0.bumpBal⟩, ⟨ck, jStar⟩)
  guess st cStar := do
    let (ivStar, dStar, qs) ← runBadH5WithChallenge setup st.ck st.jStar cStar
    let m0 := setup.msgs st.ck st.jStar
    return qs.any fun q =>
      decide (q.iv = ivStar) &&
        decide (setup.Com.eval st.ck m0 (q.label + setup.baseLabel st.ck st.jStar q.gate +
          dStar) = cStar)

/-- Explicit commitment-binding reduction extracting a `BindingCollision` between `msgs ck j*`
and `(msgs ck j*).bumpBal` whenever `badH5HidingReduction` hits under `b_hide = true`. -/
noncomputable def badH5BindingReduction [DecidableEq C] [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    [NeZero qTok] (ck : CommitKey) :
    ProbComp (Commitment.BindingCollision (CommitMsg Nullifier Context) C (Fin lam → ZMod 2)) := do
  let jStar ← ProbComp.uniform (Fin qTok)
  let rDummy ← setup.Com.openSample
  let m0 := setup.msgs ck jStar
  let cStar := setup.Com.eval ck m0.bumpBal rDummy
  let (ivStar, dStar, qs) ← runBadH5WithChallenge setup ck jStar cStar
  let found? := qs.find? fun q =>
    decide (q.iv = ivStar) &&
      decide (setup.Com.eval ck m0 (q.label + setup.baseLabel ck jStar q.gate + dStar) = cStar)
  match found? with
  | some q =>
    return {
      commitment := cStar
      msg₀ := m0
      opening₀ := q.label + setup.baseLabel ck jStar q.gate + dStar
      msg₁ := m0.bumpBal
      opening₁ := rDummy
    }
  | none =>
    return {
      commitment := cStar
      msg₀ := m0
      opening₀ := 0
      msg₁ := m0
      opening₁ := 0
    }

/-- **Non-black-box CRT witness-reuse decoupling (`G8 → G8.5`)** (original to this library, where
`G8` follows [BaumEtAl2026FAEST] §10.10 Theorem 10.42 and `G8.5` is this library's intermediate
hop): assuming `0 < qTok` (`NeZero qTok`), any `H5`-adaptive distinguisher over the `qTok`
non-adaptive `ck`-fixed token bundles (`r j` as witness prefix in `r`-first layout, raw-`H5`
`cmult`) has advantage between coupled `g8Game` and decoupled `g85Game` at most
`qTok * (Adv^hide + Pr[binding]) + g85IvCollisionProb` via `badH5HidingReduction` and
`badH5BindingReduction` (`g85IvCollisionProb` tracks IV injectivity instead of a fixed `2 ^ (-λ)`
term, and composition with `G1–G8` remains `#7068`). -/
theorem crtDecouple_advantage_le [DecidableEq C] [Fintype IV]
    [DecidableEq Nullifier] [DecidableEq Context]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    [NeZero qTok] :
    (Game.advantage (g8Game setup) (g85Game setup) : ℝ) ≤
      (qTok : ℝ) *
        ((Experiment.advantage
          (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false)
          (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) true) : ℝ) +
          (Experiment.succProbability
            (setup.Com.toScheme.bindingExperiment (badH5BindingReduction setup)) : ℝ)) +
        g85IvCollisionProb setup := by
  let logRun : CommitKey → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
      (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → IV) →
      (Fin qTok → Fin nMult → Fin nMask → ZMod 2) →
      PMF (Bool × List (H5Query IV nMult lam)) := fun ck h5 r d iv cmult =>
    let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
      ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
    ProbOracleComp.runWith (h5LogHandler h5) (setup.adv ck tok) []
  let badRun : CommitKey → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
      (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → IV) →
      (Fin qTok → Fin nMult → Fin nMask → ZMod 2) → PMF (Bool × Bool) :=
    fun ck h5 r d iv cmult =>
      let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
        ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
      ProbOracleComp.runWith (g85Handler setup ck iv d r h5) (setup.adv ck tok) false
  have hlog_to_bad (ck : CommitKey) (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
      (r d : Fin qTok → Fin lam → ZMod 2) (iv : Fin qTok → IV)
      (cmult : Fin qTok → Fin nMult → Fin nMask → ZMod 2) :
      (logRun ck h5 r d iv cmult).map (fun (a, qs) => (a, qs.any (isBadH5Query setup ck iv d r))) =
        badRun ck h5 r d iv cmult := by
    refine ProbOracleComp.runWith_map_state (h5LogHandler h5) (g85Handler setup ck iv d r h5)
      (fun qs => qs.any (isBadH5Query setup ck iv d r))
      (fun q qs => by simp [h5LogHandler, g85Handler, Bool.or_comm]) _ []
  let outerSetup {α : Type} :
      (CommitKey → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) →
        (Fin qTok → IV) → PMF α) → PMF α := fun f =>
    (ProbComp.eval setup.Com.keyGen).bind fun ck =>
    (ProbComp.eval (samplePi qTok (fun _ => setup.Com.openSample))).bind fun r =>
    (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind fun d =>
    (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv => f ck r d iv
  let fullSetup {α : Type} :
      (CommitKey → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) →
        (Fin qTok → IV) → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
        (Fin qTok → Fin nMult → Fin nMask → ZMod 2) → PMF α) → PMF α := fun f =>
    outerSetup fun ck r d iv =>
      (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
      (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
        f ck r d iv h5 cmult
  have hbindSum : ∀ {α : Type} (p : PMF α) (f g h : α → ℝ≥0∞),
      (∀ x, f x ≤ g x + h x) →
      (∑' x, p x * f x) ≤ (∑' x, p x * g x) + (∑' x, p x * h x) := by
    intro α p f g h hle
    rw [← tsum_add]
    exact tsum_le_tsum fun x => (mul_add (p x) (g x) (h x)).symm ▸
      mul_le_mul_of_nonneg_left (hle x) zero_le
  have hfullCongr : ∀ {α : Type} (f g :
      CommitKey → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) →
        (Fin qTok → IV) → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
        (Fin qTok → Fin nMult → Fin nMask → ZMod 2) → PMF α),
      (∀ ck r d iv h5 cmult, f ck r d iv h5 cmult = g ck r d iv h5 cmult) →
      fullSetup f = fullSetup g := fun f g h =>
    pmfBind_congr _ fun ck => pmfBind_congr _ fun r => pmfBind_congr _ fun d =>
      pmfBind_congr _ fun iv => pmfBind_congr _ fun h5 => pmfBind_congr _ fun cmult =>
        h ck r d iv h5 cmult
  have hfullMap : ∀ {α β : Type} (f :
      CommitKey → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) →
        (Fin qTok → IV) → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
        (Fin qTok → Fin nMult → Fin nMask → ZMod 2) → PMF α) (g : α → β),
      (fullSetup f).map g =
        fullSetup fun ck r d iv h5 cmult => (f ck r d iv h5 cmult).map g := by
    intro α β f g
    simp only [fullSetup, outerSetup, PMF.map_bind]
  have hg85_eq :
      g85Game setup =
        (ProbComp.eval setup.Com.keyGen).bind fun ck =>
        (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
        (ProbComp.eval (samplePi qTok (fun _ => setup.Com.openSample))).bind fun r =>
        (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind fun d =>
        (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv =>
        (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
        (badRun ck h5 r d iv cmult).map Prod.fst := by
    simp only [g85Game, g85FullRun, badRun, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.map_bind]
    refine pmfBind_congr _ fun ck => pmfBind_congr _ fun h5 =>
      pmfBind_congr _ fun r => pmfBind_congr _ fun d =>
      pmfBind_congr _ fun iv => pmfBind_congr _ fun cmult => ?_
    rw [ProbOracleComp.eval_runState]
    have hg85 : (fun q state => ProbComp.eval (g85HandlerP setup ck iv d r h5 q state)) =
        g85Handler setup ck iv d r h5 :=
      funext fun q => funext fun s => by simp [g85HandlerP, g85Handler]
    rw [hg85]
    simp only [PMF.map, Function.comp_def, PMF.pure_bind]
  have hg8_eq :
      g8Game setup =
        fullSetup fun ck r d iv h5 _ =>
          let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
            ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
              fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + d j + r j⟩⟩
          ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5 q))) := by
    simp only [fullSetup, outerSetup, g8Game, ProbComp.eval_bind, ProbComp.eval_uniform]
    refine pmfBind_congr _ fun ck => ?_
    rw [PMF.bind_comm]
    refine pmfBind_congr _ fun r => ?_
    have hvec : ∀ v : Fin lam → ZMod 2, v + v = 0 :=
      fun v => funext fun k => CharTwo.add_self_eq_zero (v k)
    let eAdd : (Fin qTok → Fin lam → ZMod 2) ≃ (Fin qTok → Fin lam → ZMod 2) :=
      { toFun := fun u j => r j + u j
        invFun := fun d j => d j + r j
        left_inv := fun u => funext fun j => by
          dsimp only
          rw [add_comm (r j) (u j), add_assoc, hvec, add_zero]
        right_inv := fun d => funext fun j => by
          dsimp only
          rw [add_comm (d j) (r j), ← add_assoc, hvec, zero_add] }
    have hshift :
        (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind (fun u =>
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, r j + u j,
                  fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + u j⟩⟩
              ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5 q)))) =
        (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind (fun d =>
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
                  fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + d j + r j⟩⟩
              ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5 q)))) := by
      conv_rhs => rw [← uniformOfFintype_map_equiv eAdd, PMF.bind_map]
      simp only [Function.comp_def, eAdd, Equiv.coe_fn_mk]
      refine pmfBind_congr _ fun u => pmfBind_congr _ fun h5 => pmfBind_congr _ fun iv => ?_
      have hlab : ∀ j e,
          setup.baseLabel ck j e + (r j + u j) + r j = setup.baseLabel ck j e + u j :=
        fun j e => by
          rw [add_assoc (setup.baseLabel ck j e), add_comm (r j) (u j), add_assoc,
            hvec, add_zero]
      simp_rw [hlab]
    rw [PMF.bind_comm]
    rw [hshift]
    refine pmfBind_congr _ fun d => ?_
    rw [PMF.bind_comm]
    refine pmfBind_congr _ fun iv => pmfBind_congr _ fun h5 => ?_
    exact (PMF.bind_const _ _).symm
  have hdec_point :
      ∀ ck r d iv,
        let P : Game :=
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
                  fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + d j + r j⟩⟩
              ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5 q)))
        let Q : Game :=
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              (badRun ck h5 r d iv cmult).map Prod.fst
        let B : ℝ≥0∞ :=
          if Function.Injective iv then
            ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
              (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
                (badRun ck h5 r d iv cmult).map Prod.snd) true
          else 1
        P true ≤ Q true + B ∧ Q true ≤ P true + B := by
    intro ck r d iv P Q B
    by_cases hInj : Function.Injective iv
    · simp only [B, hInj, ↓reduceIte]
      have hphiInj :
          Function.Injective (fun p : Fin qTok × Fin nMult =>
            badH5Key setup ck iv d r p.1 p.2) := by
        intro p₁ p₂ hp
        have hiv : iv p₁.1 = iv p₂.1 := congrArg H5Query.iv hp
        have hgate : p₁.2 = p₂.2 := congrArg H5Query.gate hp
        exact Prod.ext (hInj hiv) hgate
      let φ : Fin qTok × Fin nMult → H5Query IV nMult lam :=
        fun p => badH5Key setup ck iv d r p.1 p.2
      let eSwap :
          ((Fin qTok → Fin nMult → Fin nMask → ZMod 2) ×
              (H5Query IV nMult lam → Fin nMask → ZMod 2)) ≃
            ((Fin qTok → Fin nMult → Fin nMask → ZMod 2) ×
              (H5Query IV nMult lam → Fin nMask → ZMod 2)) := by
        classical
        exact
          { toFun := fun ⟨cmult, h5⟩ =>
              (fun j e => h5 (φ (j, e)),
                fun q => if h : ∃ p, φ p = q then
                  cmult (Classical.choose h).1 (Classical.choose h).2
                  else h5 q)
            invFun := fun ⟨cmult, h5⟩ =>
              (fun j e => h5 (φ (j, e)),
                fun q => if h : ∃ p, φ p = q then
                  cmult (Classical.choose h).1 (Classical.choose h).2
                  else h5 q)
            left_inv := fun ⟨cmult, h5⟩ => by
              ext1
              · funext j e
                have hex : ∃ p, φ p = φ (j, e) := ⟨(j, e), rfl⟩
                have hch : Classical.choose hex = (j, e) := hphiInj (Classical.choose_spec hex)
                simp [hex, hch]
              · funext q
                by_cases hq : ∃ p, φ p = q
                · rcases hq with ⟨p, rfl⟩
                  have hex : ∃ p', φ p' = φ p := ⟨p, rfl⟩
                  have hch : Classical.choose hex = p := hphiInj (Classical.choose_spec hex)
                  simp only [hex, ↓reduceDIte, hch]
                · simp [hq]
            right_inv := fun ⟨cmult, h5⟩ => by
              ext1
              · funext j e
                have hex : ∃ p, φ p = φ (j, e) := ⟨(j, e), rfl⟩
                have hch : Classical.choose hex = (j, e) := hphiInj (Classical.choose_spec hex)
                simp [hex, hch]
              · funext q
                by_cases hq : ∃ p, φ p = q
                · rcases hq with ⟨p, rfl⟩
                  have hex : ∃ p', φ p' = φ p := ⟨p, rfl⟩
                  have hch : Classical.choose hex = p := hphiInj (Classical.choose_spec hex)
                  simp only [hex, ↓reduceDIte, hch]
                · simp [hq] }
      have hP_eq :
          P = (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
              (ProbOracleComp.runWith (g8Handler setup ck iv d r cmult h5) (setup.adv ck tok)
                false).map Prod.fst := by
        have hprod : P =
            (uniformOfFintype ((Fin qTok → Fin nMult → Fin nMask → ZMod 2) ×
              (H5Query IV nMult lam → Fin nMask → ZMod 2))).bind fun ⟨cmult, h5⟩ =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
                  fun e => h5 (φ (j, e))⟩
              ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5 q))) := by
          simp only [P]
          rw [← uniformOfFintype_prod, PMF.bind_bind]
          simp only [PMF.bind_map, Function.comp_def]
          rw [PMF.bind_comm]
          rfl
        have hprod2 :
            ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
              (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
                let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                  ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
                (ProbOracleComp.runWith (g8Handler setup ck iv d r cmult h5) (setup.adv ck tok)
                  false).map Prod.fst) =
            ((uniformOfFintype ((Fin qTok → Fin nMult → Fin nMask → ZMod 2) ×
              (H5Query IV nMult lam → Fin nMask → ZMod 2))).map eSwap).bind fun ⟨cmult', h5'⟩ =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
                  fun e => h5' (φ (j, e))⟩
              ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5' q))) := by
          rw [PMF.bind_map, ← uniformOfFintype_prod, PMF.bind_bind]
          simp only [PMF.bind_map, Function.comp_def]
          rw [PMF.bind_comm]
          simp only [eSwap, Equiv.coe_fn_mk]
          refine pmfBind_congr _ fun cmult => pmfBind_congr _ fun h5 => ?_
          have hg8_ans : ∀ q (s : Bool),
              ((g8Handler setup ck iv d r cmult h5 q s).map fun (a, _) => (a, ())) =
              PMF.pure ((if h : ∃ p, φ p = q then
                cmult (Classical.choose h).1 (Classical.choose h).2 else h5 q), ()) := by
            intro q s
            simp only [g8Handler]
            by_cases h1 : ∃ p, q = φ p <;> by_cases h2 : ∃ p, φ p = q
            · dsimp only [φ] at h1 h2 ⊢
              have hch : Classical.choose h1 = Classical.choose h2 :=
                hphiInj ((Classical.choose_spec h1).symm.trans (Classical.choose_spec h2).symm)
              simp [h1, h2, hch]
            · rcases h1 with ⟨p, hp⟩
              exact absurd ⟨p, hp.symm⟩ h2
            · rcases h2 with ⟨p, hp⟩
              exact absurd ⟨p, hp.symm⟩ h1
            · dsimp only [φ] at h1 h2 ⊢
              simp [h1, h2]
          have hunit := ProbOracleComp.runWith_map_state
            (g8Handler setup ck iv d r cmult h5)
            (fun q (_ : Unit) => PMF.pure ((if h : ∃ p, φ p = q then
              cmult (Classical.choose h).1 (Classical.choose h).2 else h5 q), ()))
            (fun _ => ()) (fun q s => hg8_ans q s)
            (setup.adv ck fun j => ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩)
            false
          have hmap1 :
              ((ProbOracleComp.runWith (g8Handler setup ck iv d r cmult h5)
                (setup.adv ck fun j => ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
                  cmult j⟩) false).map Prod.fst) =
              (((ProbOracleComp.runWith (g8Handler setup ck iv d r cmult h5)
                (setup.adv ck fun j => ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
                  cmult j⟩) false).map (fun (a, s') => (a, ()))).map Prod.fst) := by
            rw [PMF.map_comp]; rfl
          rw [hmap1, hunit]
          have hro := ProbOracleComp.runWith_readOnly
            (fun q (_ : Unit) => PMF.pure (if h : ∃ p, φ p = q then
              cmult (Classical.choose h).1 (Classical.choose h).2 else h5 q))
            (setup.adv ck fun j => ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩)
            ()
          have hcm : (fun j e =>
              (if h : ∃ p, φ p = φ (j, e) then cmult (Classical.choose h).1 (Classical.choose h).2
                else h5 (φ (j, e)))) = cmult := by
            funext j e
            have hex : ∃ p, φ p = φ (j, e) := ⟨(j, e), rfl⟩
            have hch : Classical.choose hex = (j, e) := hphiInj (Classical.choose_spec hex)
            simp [hex, hch]
          simp only [φ] at hcm hro ⊢
          rw [show (fun q (_ : Unit) =>
              PMF.pure (if h : ∃ p : Fin qTok × Fin nMult,
                  badH5Key setup ck iv d r p.1 p.2 = q then
                cmult (Classical.choose h).1 (Classical.choose h).2 else h5 q, ())) =
              fun q state => (PMF.pure (if h : ∃ p : Fin qTok × Fin nMult,
                  badH5Key setup ck iv d r p.1 p.2 = q then
                cmult (Classical.choose h).1 (Classical.choose h).2 else h5 q)).map
                  (·, state) from
            funext fun q => funext fun s => by cases s; simp]
          rw [hro, PMF.map_comp]
          rw [show (Prod.fst ∘ fun x : Bool => (x, ())) = id from rfl, PMF.map_id,
            OracleComp.evalWith_eq_interpret, ProbOracleComp.eval_run]
          congr 1
          congr 1
          funext j
          congr 1
          exact (congrFun hcm j).symm
        rw [hprod, hprod2, uniformOfFintype_map_equiv eSwap]
      have hstep_le : ∀ h5 cmult,
          let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
            ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
          let firstRun := ProbOracleComp.runWith (g8Handler setup ck iv d r cmult h5)
            (setup.adv ck tok) false
          let secondRun := ProbOracleComp.runWith (g85Handler setup ck iv d r h5)
            (setup.adv ck tok) false
          (firstRun.map Prod.fst) true ≤
            (secondRun.map Prod.fst) true + (secondRun.map Prod.snd) true ∧
          (secondRun.map Prod.fst) true ≤
            (firstRun.map Prod.fst) true + (secondRun.map Prod.snd) true := by
        intro h5 cmult tok firstRun secondRun
        have hub := crtDecouple_identicalUntilBad setup ck iv d r cmult h5
        have h1 := hub.bind_apply_le (setup.adv ck tok) false
          (fun x => PMF.pure x.1) true
        have h2 := hub.symm.bind_apply_le (setup.adv ck tok) false
          (fun x => PMF.pure x.1) true
        rw [hub.bad_eq (setup.adv ck tok) false] at h1
        simp_rw [← ProbOracleComp.runWith_eq_run_interpret] at h1 h2
        have hbadSet :
            (ProbOracleComp.runWith (g85Handler setup ck iv d r h5)
              (setup.adv ck tok) false).toOuterMeasure {x | x.2 = true} =
              (secondRun.map Prod.snd) true := by
          rw [PMF.toOuterMeasure_apply, PMF.map_apply]
          refine tsum_congr fun x => ?_
          by_cases hx : x.2 = true
          · simp [hx, secondRun]
          · simp [hx]
        rw [hbadSet] at h1 h2
        exact ⟨by simpa [firstRun, secondRun, PMF.map, Function.comp_def] using h1,
          by simpa [firstRun, secondRun, PMF.map, Function.comp_def] using h2⟩
      have hbind2 : ∀ {α : Type} (p : PMF α) (f g h : α → ℝ≥0∞),
          (∀ x, f x ≤ g x + h x) →
          (∑' x, p x * f x) ≤ (∑' x, p x * g x) + (∑' x, p x * h x) := by
        intro α p f g h hle
        rw [← tsum_add]
        exact tsum_le_tsum fun x => (mul_add (p x) (g x) (h x)).symm ▸
          mul_le_mul_of_nonneg_left (hle x) zero_le
      rw [hP_eq]
      constructor
      · simp only [Q, badRun, PMF.bind_apply]
        exact hbindSum _ _ _ _ fun h5 => hbindSum _ _ _ _ fun cmult => (hstep_le h5 cmult).1
      · simp only [Q, badRun, PMF.bind_apply]
        exact hbindSum _ _ _ _ fun h5 => hbindSum _ _ _ _ fun cmult => (hstep_le h5 cmult).2
    · simp only [B, hInj, ↓reduceIte]
      exact ⟨le_trans (PMF.coe_le_one _ _) le_add_self,
        le_trans (PMF.coe_le_one _ _) le_add_self⟩
  let badFullProb : ℝ≥0∞ := ((ProbComp.eval (g85FullRun setup)).map fun (_, bad, _) => bad) true
  let ivFullProb : ℝ≥0∞ :=
    ((ProbComp.eval (g85FullRun setup)).map fun (_, _, ivColl) => ivColl) true
  have hg85_reorder :
      ProbComp.eval (g85FullRun setup) =
        fullSetup fun ck r d iv h5 cmult =>
          (badRun ck h5 r d iv cmult).map fun res =>
            (res.1, res.2, decide (¬ Function.Injective iv)) := by
    simp only [fullSetup, outerSetup, g85FullRun, badRun, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure]
    refine pmfBind_congr _ fun ck => ?_
    rw [PMF.bind_comm]; refine pmfBind_congr _ fun r => ?_
    rw [PMF.bind_comm]; refine pmfBind_congr _ fun d => ?_
    rw [PMF.bind_comm]; refine pmfBind_congr _ fun iv => ?_
    refine pmfBind_congr _ fun h5 => pmfBind_congr _ fun cmult => ?_
    rw [ProbOracleComp.eval_runState]
    have hg85 : (fun q state => ProbComp.eval (g85HandlerP setup ck iv d r h5 q state)) =
        g85Handler setup ck iv d r h5 :=
      funext fun q => funext fun s => by simp [g85HandlerP, g85Handler]
    rw [hg85]
    simp only [PMF.map, Function.comp_def]
  have hdec_global :
      g8Game setup true ≤ g85Game setup true + (badFullProb + ivFullProb) ∧
      g85Game setup true ≤ g8Game setup true + (badFullProb + ivFullProb) := by
    have hbad_le : ∀ ck r d iv,
        (if Function.Injective iv then
          ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              (badRun ck h5 r d iv cmult).map Prod.snd) true
        else (1 : ℝ≥0∞)) ≤
          ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              (badRun ck h5 r d iv cmult).map Prod.snd) true +
            (PMF.pure (decide (¬ Function.Injective iv))) true := by
      intro ck r d iv
      by_cases hInj : Function.Injective iv
      · simp [hInj]
      · simp [hInj, self_le_add_left]
    have hg85_fst :
        g85Game setup true =
          (fullSetup fun ck r d iv h5 cmult => (badRun ck h5 r d iv cmult).map Prod.fst) true := by
      rw [g85Game, hg85_reorder, hfullMap]
      refine congrArg (fun p : PMF Bool => p true) (hfullCongr _ _ fun ck r d iv h5 cmult => ?_)
      rw [PMF.map_comp]; rfl
    have hsum_bad :
        badFullProb + ivFullProb =
          (fullSetup fun ck r d iv h5 cmult => (badRun ck h5 r d iv cmult).map Prod.snd) true +
          (outerSetup fun _ _ _ iv => PMF.pure (decide (¬ Function.Injective iv))) true := by
      simp only [badFullProb, ivFullProb, hg85_reorder]
      congr 1
      · rw [hfullMap]
        refine congrArg (fun p : PMF Bool => p true) (hfullCongr _ _ fun _ _ _ _ _ _ => ?_)
        rw [PMF.map_comp]; rfl
      · simp only [fullSetup, outerSetup, PMF.map_bind]
        refine congrArg (fun p : PMF Bool => p true) ?_
        refine pmfBind_congr _ fun ck => pmfBind_congr _ fun r =>
          pmfBind_congr _ fun d => pmfBind_congr _ fun iv => ?_
        simp [PMF.map, Function.comp_def, PMF.bind_const]
    rw [hg8_eq, hg85_fst, hsum_bad]
    constructor
    · simp only [fullSetup, outerSetup, PMF.bind_apply]
      refine le_trans (hbindSum _ _ _ _ fun ck =>
        hbindSum _ _ _ _ fun r =>
        hbindSum _ _ _ _ fun d =>
        hbindSum _ _ _ _ fun iv =>
          le_trans (hdec_point ck r d iv).1 (add_le_add (le_refl _) (hbad_le ck r d iv))) ?_
      simp only [mul_add, tsum_add, PMF.bind_apply]
      exact le_refl _
    · simp only [fullSetup, outerSetup, PMF.bind_apply]
      refine le_trans (hbindSum _ _ _ _ fun ck =>
        hbindSum _ _ _ _ fun r =>
        hbindSum _ _ _ _ fun d =>
        hbindSum _ _ _ _ fun iv =>
          le_trans (hdec_point ck r d iv).2 (add_le_add (le_refl _) (hbad_le ck r d iv))) ?_
      simp only [mul_add, tsum_add, PMF.bind_apply]
      exact le_refl _
  have hbad_hide :
      badFullProb ≤ (qTok : ℝ≥0∞) *
        (ProbComp.eval
          (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false) true) := by
    have hq_pos : (qTok : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast NeZero.ne qTok
    have hq_ne_top : (qTok : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top qTok
    have hhide_re :
        ProbComp.eval (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false) =
          fullSetup fun ck r d iv h5 cmult =>
            (logRun ck h5 r d iv cmult).bind fun res =>
              (uniformOfFintype (Fin qTok)).map fun jStar =>
                res.2.any fun q =>
                  decide (q.iv = iv jStar) &&
                    decide (setup.Com.eval ck (setup.msgs ck jStar)
                      (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
                      setup.Com.eval ck (setup.msgs ck jStar) (r jStar)) := by
      simp only [fullSetup, outerSetup, Commitment.Scheme.eval_hidingExperiment, Game.withSetup,
        eval_lrExperiment, badH5HidingReduction, runBadH5WithChallenge,
        OpeningCommitment.toScheme, Commitment.Scheme.commitment, MessagePair.select_false,
        ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform, ProbComp.eval_pure,
        PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, ite_true, logRun]
      refine pmfBind_congr _ fun ck => ?_
      have hcomm1 : ∀ (jStar : Fin qTok),
          ((ProbComp.eval setup.Com.openSample).bind fun rStar =>
            (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (ProbComp.eval (samplePi qTok (fun j => if j = jStar then pure (0 : Fin lam → ZMod 2)
              else setup.Com.openSample))).bind fun rOthers =>
            (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind fun d =>
            (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨if j = jStar then setup.Com.eval ck (setup.msgs ck jStar) rStar
                  else setup.Com.eval ck (setup.msgs ck j) (rOthers j), iv j, d j, cmult j⟩
              (ProbComp.eval (((setup.adv ck tok).runState (h5LogHandlerP h5)).run [])).bind
                fun res =>
                  PMF.pure (res.2.any fun q =>
                    decide (q.iv = iv jStar) &&
                      decide (setup.Com.eval ck (setup.msgs ck jStar)
                        (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
                        setup.Com.eval ck (setup.msgs ck jStar) rStar))) =
          ((ProbComp.eval (samplePi qTok (fun _ => setup.Com.openSample))).bind fun r =>
            (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind fun d =>
            (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv =>
            (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              (ProbOracleComp.runWith (h5LogHandler h5) (setup.adv ck fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩) []).bind
                fun res =>
                  PMF.pure (res.2.any fun q =>
                    decide (q.iv = iv jStar) &&
                      decide (setup.Com.eval ck (setup.msgs ck jStar)
                        (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
                        setup.Com.eval ck (setup.msgs ck jStar) (r jStar)))) := by
        intro jStar
        have hrep := samplePi_replace (fun _ : Fin qTok => setup.Com.openSample)
          (fun _ : Fin qTok => (0 : Fin lam → ZMod 2)) jStar
        rw [← hrep]
        simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
        conv_lhs => enter [2, rStar]; rw [PMF.bind_comm]
        rw [PMF.bind_comm]
        refine pmfBind_congr _ fun rOthers => pmfBind_congr _ fun rStar => ?_
        conv_rhs => rw [pmfBind_comm2]
        refine pmfBind_congr _ fun h5 => pmfBind_congr _ fun d =>
          pmfBind_congr _ fun iv => pmfBind_congr _ fun cmult => ?_
        have heq_tok : ∀ (d : Fin qTok → Fin lam → ZMod 2) (iv : Fin qTok → IV)
            (cmult : Fin qTok → Fin nMult → Fin nMask → ZMod 2),
            (fun j : Fin qTok =>
              (⟨if j = jStar then setup.Com.eval ck (setup.msgs ck jStar) rStar
                else setup.Com.eval ck (setup.msgs ck j) (rOthers j), iv j, d j, cmult j⟩ :
                  CRTProofToken C IV nMult lam nMask)) =
              (fun j : Fin qTok =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (Function.update rOthers jStar rStar j),
                  iv j, d j, cmult j⟩) := by
          intro d iv cmult
          funext j
          by_cases hj : j = jStar
          · subst hj; simp [Function.update]
          · simp [hj, Function.update]
        have hup : Function.update rOthers jStar rStar jStar = rStar := by simp
        simp only [heq_tok, hup]
        rw [ProbOracleComp.eval_runState]
        have hh5 : (fun q state => ProbComp.eval (h5LogHandlerP h5 q state)) =
            h5LogHandler h5 :=
          funext fun q => funext fun s => by simp [h5LogHandlerP, h5LogHandler]
        rw [hh5]
      simp_rw [hcomm1]
      rw [PMF.bind_comm]; refine pmfBind_congr _ fun r => ?_
      rw [PMF.bind_comm]; refine pmfBind_congr _ fun d => ?_
      rw [PMF.bind_comm]; refine pmfBind_congr _ fun iv => ?_
      rw [PMF.bind_comm]; refine pmfBind_congr _ fun h5 => ?_
      rw [PMF.bind_comm]; refine pmfBind_congr _ fun cmult => ?_
      rw [PMF.bind_comm]
      simp [PMF.map, Function.comp_def]
    rw [hhide_re]
    have hbad_eq :
        badFullProb =
          (fullSetup fun ck r d iv h5 cmult =>
            (logRun ck h5 r d iv cmult).bind fun res =>
              PMF.pure (res.2.any (isBadH5Query setup ck iv d r))) true := by
      simp only [badFullProb, hg85_reorder]
      rw [hfullMap]
      refine congrArg (fun p : PMF Bool => p true) (hfullCongr _ _ fun ck r d iv h5 cmult => ?_)
      rw [← hlog_to_bad ck h5 r d iv cmult]
      simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    rw [hbad_eq]
    have hpoint_hit : ∀ (ck : CommitKey) (r d : Fin qTok → Fin lam → ZMod 2)
        (iv : Fin qTok → IV) (qs : List (H5Query IV nMult lam)),
        (PMF.pure (qs.any (isBadH5Query setup ck iv d r))) true ≤
          (qTok : ℝ≥0∞) *
            ((uniformOfFintype (Fin qTok)).map fun jStar =>
              qs.any fun q =>
                decide (q.iv = iv jStar) &&
                  decide (setup.Com.eval ck (setup.msgs ck jStar)
                    (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
                    setup.Com.eval ck (setup.msgs ck jStar) (r jStar))) true := by
      intro ck r d iv qs
      by_cases hhit : qs.any (isBadH5Query setup ck iv d r) = true
      · simp only [hhit, PMF.pure_apply, ↓reduceIte]
        rcases List.any_eq_true.mp hhit with ⟨q, hqmem, hqbad⟩
        simp only [isBadH5Query, decide_eq_true_eq] at hqbad
        rcases hqbad with ⟨j₀, e₀, rfl⟩
        have hpred0 : (qs.any fun q =>
            decide (q.iv = iv j₀) &&
              decide (setup.Com.eval ck (setup.msgs ck j₀)
                (q.label + setup.baseLabel ck j₀ q.gate + d j₀) =
                setup.Com.eval ck (setup.msgs ck j₀) (r j₀))) = true := by
          refine List.any_eq_true.mpr ⟨badH5Key setup ck iv d r j₀ e₀, hqmem, ?_⟩
          have hvec : ∀ v : Fin lam → ZMod 2, v + v = 0 :=
            fun v => funext fun k => CharTwo.add_self_eq_zero (v k)
          have hlab : (setup.baseLabel ck j₀ e₀ + d j₀ + r j₀) +
              setup.baseLabel ck j₀ e₀ + d j₀ = r j₀ := by
            rw [add_assoc _ _ (d j₀), add_comm _ (r j₀), add_assoc,
              hvec, add_zero]
          simp [badH5Key, hlab]
        have hle1 : (qTok : ℝ≥0∞)⁻¹ ≤
            ((uniformOfFintype (Fin qTok)).map fun jStar =>
              qs.any fun q =>
                decide (q.iv = iv jStar) &&
                  decide (setup.Com.eval ck (setup.msgs ck jStar)
                    (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
                    setup.Com.eval ck (setup.msgs ck jStar) (r jStar))) true := by
          rw [PMF.map_apply]
          have hj0 : (qTok : ℝ≥0∞)⁻¹ =
              if true = (qs.any fun q =>
                  decide (q.iv = iv j₀) &&
                    decide (setup.Com.eval ck (setup.msgs ck j₀)
                      (q.label + setup.baseLabel ck j₀ q.gate + d j₀) =
                      setup.Com.eval ck (setup.msgs ck j₀) (r j₀)))
                then (uniformOfFintype (Fin qTok)) j₀ else 0 := by
            simp [uniformOfFintype_apply, hpred0]
          simpa using hj0.trans_le (le_tsum
            (f := fun jStar =>
              if true = (qs.any fun q =>
                  decide (q.iv = iv jStar) &&
                    decide (setup.Com.eval ck (setup.msgs ck jStar)
                      (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
                      setup.Com.eval ck (setup.msgs ck jStar) (r jStar)))
                then (uniformOfFintype (Fin qTok)) jStar else 0) j₀)
        calc (1 : ℝ≥0∞) = (qTok : ℝ≥0∞) * (qTok : ℝ≥0∞)⁻¹ :=
              (ENNReal.mul_inv_cancel hq_pos hq_ne_top).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hle1 zero_le
      · simp [Bool.eq_false_iff.mpr hhit]
    have hmul_bind : ∀ {α : Type} (p : PMF α) (f g : α → ℝ≥0∞),
        (∀ x, f x ≤ (qTok : ℝ≥0∞) * g x) →
        (∑' x, p x * f x) ≤ (qTok : ℝ≥0∞) * (∑' x, p x * g x) := by
      intro α p f g hle
      rw [← ENNReal.tsum_mul_left]
      refine tsum_le_tsum fun x => ?_
      calc p x * f x ≤ p x * ((qTok : ℝ≥0∞) * g x) := mul_le_mul_of_nonneg_left (hle x) zero_le
        _ = (qTok : ℝ≥0∞) * (p x * g x) := by ring
    simp only [fullSetup, outerSetup, PMF.bind_apply]
    exact hmul_bind _ _ _ fun ck => hmul_bind _ _ _ fun r => hmul_bind _ _ _ fun d =>
      hmul_bind _ _ _ fun iv => hmul_bind _ _ _ fun h5 => hmul_bind _ _ _ fun cmult =>
      hmul_bind _ _ _ fun res => hpoint_hit ck r d iv res.2
  have hhide_true_le_bind :
      ProbComp.eval (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) true) true ≤
        ProbComp.eval
          (setup.Com.toScheme.bindingExperiment (badH5BindingReduction setup)) true := by
    simp only [Commitment.Scheme.eval_hidingExperiment, Commitment.Scheme.bindingExperiment,
      Game.withSetup, eval_lrExperiment, badH5HidingReduction, badH5BindingReduction,
      runBadH5WithChallenge, OpeningCommitment.toScheme, Commitment.Scheme.commitment,
      MessagePair.select_true, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
      ite_true, PMF.bind_apply]
    refine tsum_le_tsum fun ck => mul_le_mul_of_nonneg_left ?_ zero_le
    refine tsum_le_tsum fun jStar => mul_le_mul_of_nonneg_left ?_ zero_le
    refine tsum_le_tsum fun rDummy => mul_le_mul_of_nonneg_left ?_ zero_le
    refine tsum_le_tsum fun h5 => mul_le_mul_of_nonneg_left ?_ zero_le
    refine tsum_le_tsum fun rOthers => mul_le_mul_of_nonneg_left ?_ zero_le
    refine tsum_le_tsum fun d => mul_le_mul_of_nonneg_left ?_ zero_le
    refine tsum_le_tsum fun iv => mul_le_mul_of_nonneg_left ?_ zero_le
    refine tsum_le_tsum fun cmult => mul_le_mul_of_nonneg_left ?_ zero_le
    refine tsum_le_tsum fun res => mul_le_mul_of_nonneg_left ?_ zero_le
    let pred : H5Query IV nMult lam → Bool := fun q =>
      decide (q.iv = iv jStar) &&
        decide (setup.Com.eval ck (setup.msgs ck jStar)
          (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
          setup.Com.eval ck (setup.msgs ck jStar).bumpBal rDummy)
    by_cases hany : res.2.any pred = true
    · dsimp only [pred] at hany
      simp only [PMF.pure_apply, hany, ↓reduceIte]
      have hfind : (res.2.find? pred).isSome = true :=
        List.find?_isSome.mpr (List.any_eq_true.mp hany)
      rcases Option.isSome_iff_exists.mp hfind with ⟨q, hq⟩
      have hqpred : pred q = true := List.find?_some hq
      have hqev : setup.Com.eval ck (setup.msgs ck jStar)
          (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
          setup.Com.eval ck (setup.msgs ck jStar).bumpBal rDummy := by
        simpa [pred] using (Bool.and_eq_true_iff.mp hqpred).2
      have hcol : setup.Com.toScheme.isBindingCollision ck
          { commitment := setup.Com.eval ck (setup.msgs ck jStar).bumpBal rDummy
            msg₀ := setup.msgs ck jStar
            opening₀ := q.label + setup.baseLabel ck jStar q.gate + d jStar
            msg₁ := (setup.msgs ck jStar).bumpBal
            opening₁ := rDummy } = true := by
        simp only [Commitment.Scheme.isBindingCollision, OpeningCommitment.toScheme,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨(CommitMsg.bumpBal_ne _).symm, hqev⟩, trivial⟩
      have hq' :
          (res.2.find? fun q =>
            decide (q.iv = iv jStar) &&
              decide (setup.Com.eval ck (setup.msgs ck jStar)
                (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
                setup.Com.eval ck (setup.msgs ck jStar).bumpBal rDummy)) = some q := hq
      rw [hq']
      dsimp only
      simp only [ProbComp.eval_pure, PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
      simp only [OpeningCommitment.toScheme] at hcol
      simp only [hcol, ↓reduceIte, le_refl]
    · dsimp only [pred] at hany
      simp only [PMF.pure_apply, Bool.eq_false_iff.mpr hany, Bool.true_eq_false, ↓reduceIte,
        zero_le]
  have hbad_real :
      badFullProb.toReal ≤
        (qTok : ℝ) *
          ((Experiment.advantage
            (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false)
            (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) true) : ℝ) +
            (Experiment.succProbability
              (setup.Com.toScheme.bindingExperiment (badH5BindingReduction setup)) : ℝ)) := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top qTok)
      (PMF.apply_ne_top _ _)) hbad_hide
    have h2 := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hhide_true_le_bind
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h1
    have h3 :
        (ProbComp.eval
          (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false) true).toReal ≤
        |(ProbComp.eval
            (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false) true).toReal -
          (ProbComp.eval
            (setup.Com.toScheme.hidingExperiment
              (badH5HidingReduction setup) true) true).toReal| +
          (ProbComp.eval
            (setup.Com.toScheme.hidingExperiment
              (badH5HidingReduction setup) true) true).toReal := by
      have hle := le_abs_self
        ((ProbComp.eval
            (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false) true).toReal -
          (ProbComp.eval
            (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) true) true).toReal)
      linarith
    rw [Experiment.coe_advantage, Experiment.coe_succProbability]
    nlinarith [Nat.cast_nonneg (α := ℝ) qTok]
  have hadv_le := Game.advantage_le_of_apply_le
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩)
    hdec_global.1 hdec_global.2
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] at hadv_le
  exact hadv_le.trans (add_le_add hbad_real (le_refl _))

end CRTDecoupling


end Cslib.Crypto.AnonymousToken.Unlinkability
