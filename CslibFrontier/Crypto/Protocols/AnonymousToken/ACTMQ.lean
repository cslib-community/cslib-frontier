/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.AnonymousToken.Basic
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
public import CslibFrontier.Crypto.Protocols.UOV.Attacks
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunLog
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Support
import Mathlib.Data.List.Dedup

/-!
# Structured-target one-more claw-freeness and VOLE-ACT-MQ credit conservation

This module formalizes the extracted-model credit-conservation reduction and structural
adversaries for VOLE-ACT-MQ ([VOLEACT2026], Instantiations / VOLE-ACT-MQ `#mq-commitment`, and
Security Considerations / Proof status `#proof-status`). Every game, reduction, and theorem in
this file is original to this library; the source draft provides neither a formal claw-freeness
game nor a security reduction.

## Scope and assumption status

* **Original interactive game (`clawExperiment`).** In VOLE-ACT-MQ, the Issuer's UOV trapdoor is
  queried on structured targets `J μ r = (F r + μ, G r)` (`Cslib.Crypto.UOV.structuredTarget`)
  combining an attacker-chosen semantic message `μ` and commitment opening `r`. Random-target
  one-more preimage resistance ([PoMFRIT2026], Definition 3.1, formalized in
  `Cslib.Crypto.Signature.oneMoreExperiment`) does not apply because targets are attacker-chosen
  rather than independently sampled, while Bouillaguet et al. (ePrint 2025/2035) formulate
  one-more claw-freeness for a uniformly random map `J` rather than the affine-homomorphic map
  `(F r + μ, G r)`. Accordingly, `clawExperiment` defines an unstudied, protocol-specific
  structured-target one-more claw-freeness experiment: the adversary queries a signing oracle on
  chosen `(μ, r)` pairs (counting distinct queried `J μ r` targets, so repeated or colliding
  target queries do not raise the budget) and must output strictly more verifying claws with
  pairwise distinct `J`-targets than distinct queried targets.
* **No named asymptotic hardness `Prop`.** All bounds are concrete inequalities relating explicit
  finite `ProbComp`/`ProbOracleComp` games and explicit query-bounded reductions; no PPT runtime
  certificate or asymptotic hardness `Prop` is asserted (tracked in #7068).
* **Explicit `G`-binding and reply-validity terms.** Because `clawExperiment` requires pairwise
  distinct output `J`-targets, a two-for-one forgery built from a `G`-collision `G r₁ = G r₂`
  with `r₁ ≠ r₂` and `F r₁ ≠ F r₂` outputs only a single target value and therefore never wins
  `clawExperiment`. `extractedExperiment_succProbability_le_structuredClaw` and
  `actMQConservation_succProbability_le` therefore include an explicit `gCollisionExperiment`
  binding term (alongside an explicit `invalidReplyExperiment` term when the certifier is not
  assumed `Signature.Scheme.Correct`). `gCollisionForger` formally witnesses that the
  `gCollisionExperiment` term cannot be dropped.

## Main definitions

* `ClawClaim`, `ClawAdversary`, `ClawExecution`, `runClaw`, `clawAccept`, `clawExperiment`:
  structured-target one-more claw-freeness experiment.
* `gCollisionAccept`, `gCollisionExperiment`: collision-resistance experiment on the binding block
  `G : Opening → Tail`.
* `anyInvalidReply`, `invalidReplyExperiment`: explicit event that an issuer oracle reply fails
  verification during an extracted run.
* `clawReduction`, `gCollisionReduction`: explicit reductions from `AnonymousToken.ExtractedForger`
  to `clawExperiment` and `gCollisionExperiment`.
* `actCom`, `actTag`, `actEmbed`: affine-homomorphic VOLE-ACT-MQ commitment and tag encoders
  matching `UOV.structuredTarget`.

## Main results

* `clawReduction_queryBound`, `actMQClawReduction_queryBound`: exact query budgets preserved from
  the extracted forger and credit-conservation adversary.
* `structuredTarget_collision`: injectivity of semantic message embedding forces any target
  collision of `UOV.structuredTarget F G (embed ·) ·` to yield `r₁ ≠ r₂` and `G r₁ = G r₂`.
* `extractedExperiment_succProbability_le_structuredClaw`: concrete bound on
  `AnonymousToken.extractedExperiment` by `clawExperiment`, `gCollisionExperiment`, and
  `invalidReplyExperiment`.
* `actMQConservation_succProbability_le`: extracted-model VOLE-ACT-MQ credit conservation from
  structured-target one-more claw-freeness and `G`-collision resistance (plus `invalidReply`
  which vanishes under `Signature.Scheme.Correct`).

## References

* [*VOLE-ACT*][VOLEACT2026], Instantiations / VOLE-ACT-MQ (`#mq-commitment`, `#mq-com`,
  `#mq-tag`), Security Considerations / MQ zero-opening scaling forgery
  (`#mq-zero-opening-forgery`), and Proof status (`#proof-status`).
* [Baum et al., *PoMFRIT*, USENIX prepublication, Definition 3.1][PoMFRIT2026].
* C. Bouillaguet, P. Frixons, P. Méaux, G. Renault, L. Simon, B. Vasseur, *Multivariate
  Commitments and Signatures with Efficient Protocols*, ePrint 2025/2035 (Table 3).
-/

public section

namespace Cslib.Crypto.AnonymousToken.ACTMQ

open Probability
open scoped ENNReal NNReal

section
variable {PK SK M R Target Sig Message Tail : Type}

@[expose] section

/-! ### Structured-target one-more claw-freeness and `G`-collision games -/

/-- A candidate claw pairing a semantic message `message : M` and commitment opening `opening : R`
with a preimage/signature `preimage : Sig` certifying `J message opening`. -/
structure ClawClaim (M R Sig : Type) where
  /-- Semantic message input to the structured target. -/
  message : M
  /-- Commitment opening input to the structured target. -/
  opening : R
  /-- Candidate signature or trapdoor preimage certifying `J message opening`. -/
  preimage : Sig
  deriving DecidableEq

/-- An adaptive adversary in the structured-target one-more claw-freeness experiment. Given the
public key `pk`, it queries a signing oracle on chosen pairs `(m, r)` to receive signatures on
`J m r`, and outputs a list of candidate claws. -/
abbrev ClawAdversary (PK M R Sig : Type) :=
  PK → ProbOracleComp (fun _ : M × R => Sig) (List (ClawClaim M R Sig))

/-- The public key, candidate claws, and ordered signing log of a structured one-more run. -/
structure ClawExecution (PK M R Sig : Type) where
  /-- Public verification key sampled by key generation. -/
  publicKey : PK
  /-- Candidate claws output by the adversary. -/
  claims : List (ClawClaim M R Sig)
  /-- Every `(m, r)` query and reply recorded in call order. -/
  log : List ((M × R) × Sig)

/-- Execute `A` against the honest signer on `J`, recording all queries and replies. -/
def runClaw (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target)
    (A : ClawAdversary PK M R Sig) : ProbComp (ClawExecution PK M R Sig) := do
  let keys ← S.keyGen
  let (claims, log) ← (A keys.1).runLog fun q => S.sign keys.2 (J q.1 q.2)
  return ⟨keys.1, claims, log⟩

/-- Acceptance predicate of the structured-target one-more claw-freeness game: the adversary
outputs strictly more claims than distinct `J`-targets queried in `run.log`, the claims' `J`-targets
are pairwise distinct, and every claim verifies under `S.verify run.publicKey`. -/
def clawAccept [DecidableEq Target] (S : Signature.Scheme PK SK Target Sig)
    (J : M → R → Target) (run : ClawExecution PK M R Sig) : Bool :=
  let queriedTargets := run.log.map fun (q, _) => J q.1 q.2
  let claimTargets := run.claims.map fun c => J c.message c.opening
  decide (queriedTargets.dedup.length < run.claims.length ∧ claimTargets.Nodup) &&
    run.claims.all fun c => S.verify run.publicKey (J c.message c.opening) c.preimage

/-- Structured-target one-more claw-freeness experiment, original to this library. Unlike
`Signature.oneMoreExperiment`, targets are adversary-chosen via `(m, r) ↦ J m r` rather than
sampled independently at random, and the oracle budget counts distinct `J`-targets queried. -/
def clawExperiment [DecidableEq Target] (S : Signature.Scheme PK SK Target Sig)
    (J : M → R → Target) (A : ClawAdversary PK M R Sig) : Experiment :=
  clawAccept S J <$> runClaw S J A

/-- Acceptance predicate for a collision `r₁ ≠ r₂` with `G r₁ = G r₂` in the binding block `G`. -/
def gCollisionAccept [DecidableEq R] [DecidableEq Tail] (G : R → Tail) :
    Option (R × R) → Bool
  | none => false
  | some (r₁, r₂) => decide (r₁ ≠ r₂ ∧ G r₁ = G r₂)

/-- Keyless collision-resistance experiment for the binding block `G : R → Tail`. -/
def gCollisionExperiment [DecidableEq R] [DecidableEq Tail] (G : R → Tail)
    (B : ProbComp (Option (R × R))) : Experiment :=
  gCollisionAccept G <$> B

/-- Whether any oracle reply in an `ExtractedForger` execution fails `S.verify`. -/
def anyInvalidReply (S : Signature.Scheme PK SK Target Sig) (target : Message → R → Target)
    (run : Execution PK Message R Sig) : Bool :=
  run.log.any fun (p, σ) => !(S.verify run.publicKey (target p.message p.opening) σ)

/-- Explicit experiment measuring whether any issuer oracle reply during `runExtracted S target B`
fails verification. Equals `PMF.pure false` when `S.Correct` holds. -/
def invalidReplyExperiment (S : Signature.Scheme PK SK Target Sig) (target : Message → R → Target)
    (B : ExtractedForger PK Message R Sig) : Experiment :=
  anyInvalidReply S target <$> runExtracted S target B

/-! ### Explicit reductions from `ExtractedForger` to `clawExperiment` and `gCollisionExperiment`
-/

/-- Pure transcript transition filtering verified log entries with pairwise distinct `J`-targets. -/
def stepValidClaim [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (pk : PK) (acc : List (ClawClaim M R Sig)) (entry : Payload Message R × Sig) :
    List (ClawClaim M R Sig) :=
  let y := J (embed entry.1.message) entry.1.opening
  if S.verify pk y entry.2 && !(acc.map fun c => J c.message c.opening).contains y then
    acc ++ [⟨embed entry.1.message, entry.1.opening, entry.2⟩]
  else
    acc

/-- Stateful query handler forwarding each semantic payload `(m, r)` to `(embed m, r)` while
recording verified claims with distinct `J`-targets. -/
def clawReductionHandler [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (pk : PK) (payload : Payload Message R) :
    StateT (List (ClawClaim M R Sig)) (ProbOracleComp (fun _ : M × R => Sig)) Sig :=
  fun acc => do
    let sig ← ProbOracleComp.query (embed payload.message, payload.opening)
    return (sig, stepValidClaim S J embed pk acc (payload, sig))

/-- Explicit reduction from `AnonymousToken.ExtractedForger` to `ClawAdversary`: runs `B` while
forwarding each query `(m, r)` to `(embed m, r)` and collecting one verified claw per distinct
queried `J`-target. When `B`'s output token verifies on a `J`-target absent from all logged
claims, prepends it to output one more verified distinct-target claw; otherwise returns `[]`. -/
def clawReduction [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (B : ExtractedForger PK Message R Sig) : ClawAdversary PK M R Sig := fun pk => do
  let (token, logged) ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (clawReductionHandler S J embed pk))
    (B pk)).run []
  let y := J (embed token.payload.message) token.payload.opening
  if S.verify pk y token.signature && !(logged.map fun c => J c.message c.opening).contains y then
    return ⟨embed token.payload.message, token.payload.opening, token.signature⟩ :: logged
  else
    return []

/-- Explicit reduction from `ExtractedForger` target collisions to `G`-collisions in `R`. -/
def gCollisionReduction [DecidableEq Target] (S : Signature.Scheme PK SK Target Sig)
    (target : Message → R → Target) (B : ExtractedForger PK Message R Sig) :
    ProbComp (Option (R × R)) :=
  (fun opt => opt.map fun w => (w.first.opening, w.second.opening)) <$>
    bindingReduction S target B

/-! ### VOLE-ACT-MQ commitment and tag encoders -/

/-- VOLE-ACT-MQ commitment `Com(nf, ctx, t, r) = (F r + encodeState nf ctx t, G r)`
([VOLEACT2026], `#mq-com`), with `encodeState nf ctx t` encoding `(nf, ctx, t, 0)` into the
message block `Message`. -/
def actCom {Nullifier Context Opening : Type} [Add Message]
    (F : Opening → Message) (G : Opening → Tail)
    (encodeState : Nullifier → Context → ℕ → Message)
    (nf : Nullifier) (ctx : Context) (t : ℕ) (r : Opening) : Message × Tail :=
  (F r + encodeState nf ctx t, G r)

/-- VOLE-ACT-MQ additive tag `Tag(c, x) = (c.1 + refundEmbed x, c.2)` ([VOLEACT2026],
`#mq-tag`), shifting only the first block without altering `G(r)`. -/
def actTag [Add Message] (refundEmbed : ℕ → Message) (c : Message × Tail) (x : ℕ) :
    Message × Tail :=
  (c.1 + refundEmbed x, c.2)

/-- Combined semantic-state and refund embedding `μ = encodeState nf ctx t + refundEmbed x` into
`Message` ([VOLEACT2026], `#mq-com` and `#mq-tag`). -/
def actEmbed {Nullifier Context : Type} [Add Message]
    (encodeState : Nullifier → Context → ℕ → Message) (refundEmbed : ℕ → Message)
    (note : Credit.Note Nullifier Context) : Message :=
  encodeState note.nullifier note.context note.credit + refundEmbed note.refund

end

/-! ### Helper lemmas and query bounds -/

/-- Any accepted `ClawExecution` contains at least one claim, and strictly more claims than
distinct `J`-targets queried in the log. -/
theorem clawAccept_imp_budget_lt [DecidableEq Target]
    {S : Signature.Scheme PK SK Target Sig} {J : M → R → Target}
    {run : ClawExecution PK M R Sig} (h : clawAccept S J run = true) :
    (run.log.map fun (q, _) => J q.1 q.2).dedup.length < run.claims.length := by
  simp only [clawAccept, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- An execution of `clawExperiment` whose claims are always empty fails unconditionally. -/
theorem clawExperiment_eq_false_of_claims_nil [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target)
    (A : ClawAdversary PK M R Sig)
    (hnil : ∀ run ∈ (ProbComp.eval (runClaw S J A)).support, run.claims = []) :
    ProbComp.eval (clawExperiment S J A) = PMF.pure false := by
  simp only [clawExperiment, ProbComp.eval_map]
  apply PMF.map_eq_pure_iff.mpr
  intro run hrun
  simp [clawAccept, hnil run hrun]

private theorem forall_mem_runLog {Q R α : Type} {O : Q → ProbComp R} {P : Q × R → Prop}
    (hO : ∀ q, ∀ r ∈ (ProbComp.eval (O q)).support, P (q, r))
    (A : ProbOracleComp (fun _ : Q => R) α) {z : α × List (Q × R)}
    (hz : z ∈ (ProbComp.eval (A.runLog O)).support) : ∀ p ∈ z.2, P p := by
  rw [ProbOracleComp.runLog, ProbOracleComp.eval_runState] at hz
  refine ProbOracleComp.runWith_invariant _ (fun log => ∀ p ∈ log, P p) ?_ A []
    (by simp) z.1 z.2 hz
  intro q log hlog r log' hstep
  simp only [ProbComp.eval_map, PMF.mem_support_map_iff, Prod.mk.injEq] at hstep
  obtain ⟨r', hr', rfl, rfl⟩ := hstep
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hlog p hp
  · exact List.mem_singleton.mp hp ▸ hO q r' hr'

/-- When `S.Correct` holds, `invalidReplyExperiment` has success probability zero. -/
theorem invalidReplyExperiment_eq_zero_of_correct
    {S : Signature.Scheme PK SK Target Sig} (hS : S.Correct)
    (target : Message → R → Target) (B : ExtractedForger PK Message R Sig) :
    Experiment.succProbability (invalidReplyExperiment S target B) = 0 := by
  have hfalse : ProbComp.eval (invalidReplyExperiment S target B) = PMF.pure false := by
    simp only [invalidReplyExperiment, ProbComp.eval_map]
    apply PMF.map_eq_pure_iff.mpr
    intro run hrun
    simp only [runExtracted, ProbComp.eval_bind, PMF.mem_support_bind_iff, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hrun
    obtain ⟨keys, hkeys, res, hres, rfl⟩ := hrun
    simp only [anyInvalidReply, List.any_eq_false, Bool.not_eq_true']
    intro entry hentry
    rw [Bool.not_eq_false]
    exact forall_mem_runLog
      (P := fun e : Payload Message R × Sig =>
        S.verify keys.1 (target e.1.message e.1.opening) e.2 = true)
      (fun p σ hσ => hS keys hkeys _ σ hσ) (B keys.1) hres entry hentry
  simp [Experiment.succProbability, Game.succProbability, hfalse]

/-- `clawReduction` makes at most `q` signing queries whenever the input `ExtractedForger` makes
at most `q` queries. No runtime bound or fair-coin efficiency follows from this query bound. -/
theorem clawReduction_queryBound [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (B : ExtractedForger PK Message R Sig) (pk : PK) {q : ℕ}
    (hB : (B pk).IsQueryBounded q) :
    (clawReduction S J embed B pk).IsQueryBounded q := by
  have hbody :
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (clawReductionHandler S J embed pk))
        (B pk)).run []).IsQueryBounded q := by
    refine OracleComp.IsCostBounded.run_interpret (fun r acc => ?_) hB []
    rcases r with k | payload
    · simpa [OracleComp.sumHandler, StateT.run, StateT.lift] using
        (ProbOracleComp.IsQueryBounded.sample
          (spec := fun _ : M × R => Sig) (ProbComp.unifFin k)).bind
          fun a => OracleComp.IsCostBounded.pure (a, acc) 0
    · simp only [OracleComp.sumHandler, Sum.elim_inr, StateT.run, clawReductionHandler]
      exact (ProbOracleComp.IsQueryBounded.query (spec := fun _ : M × R => Sig)
        (embed payload.message, payload.opening)).bind fun sig =>
          OracleComp.IsCostBounded.pure (sig, stepValidClaim S J embed pk acc (payload, sig)) 0
  have hcont : ∀ res : Token Message R Sig × List (ClawClaim M R Sig),
      ((let y := J (embed res.1.payload.message) res.1.payload.opening
        if S.verify pk y res.1.signature &&
            !(res.2.map fun c => J c.message c.opening).contains y then
          pure (⟨embed res.1.payload.message, res.1.payload.opening, res.1.signature⟩ :: res.2)
        else pure ([] : List (ClawClaim M R Sig))) :
          ProbOracleComp (fun _ : M × R => Sig) (List (ClawClaim M R Sig))).IsQueryBounded 0 := by
    intro res
    dsimp only
    split_ifs <;> exact OracleComp.IsCostBounded.pure _ 0
  exact hbody.bind hcont

/-- `Credit.target` instantiated with `actCom` and `actTag` equals `UOV.structuredTarget` at
`actEmbed`. -/
theorem credit_target_actCom_actTag {Nullifier Context Opening : Type} [AddCommGroup Message]
    (F : Opening → Message) (G : Opening → Tail)
    (encodeState : Nullifier → Context → ℕ → Message) (refundEmbed : ℕ → Message)
    (note : Credit.Note Nullifier Context) (r : Opening) :
    Credit.target (actCom F G encodeState) (actTag refundEmbed) note r =
      UOV.structuredTarget F G (actEmbed encodeState refundEmbed note) r := by
  simp [Credit.target, actCom, actTag, UOV.structuredTarget, actEmbed, add_assoc]

/-- Disjoint-slot injectivity for `actEmbed`: if `encodeState` vanishes on refund coordinates and
`refundEmbed` vanishes off refund coordinates, and both maps are injective, then `actEmbed` is
injective on `Credit.Note Nullifier Context`. -/
theorem actEmbed_injective_of_disjoint {Nullifier Context I F : Type} [AddCommGroup F]
    (isRefund : I → Bool) (encodeState : Nullifier → Context → ℕ → (I → F))
    (refundEmbed : ℕ → (I → F))
    (hstate_slot : ∀ nf ctx t i, isRefund i = true → encodeState nf ctx t i = 0)
    (hrefund_slot : ∀ x i, isRefund i = false → refundEmbed x i = 0)
    (hstate_inj : Function.Injective fun p : Nullifier × Context × ℕ => encodeState p.1 p.2.1 p.2.2)
    (hrefund_inj : Function.Injective refundEmbed) :
    Function.Injective (actEmbed encodeState refundEmbed) := by
  rintro ⟨nf₁, ctx₁, t₁, x₁⟩ ⟨nf₂, ctx₂, t₂, x₂⟩ heq
  have hrefund_eq : refundEmbed x₁ = refundEmbed x₂ := by
    funext i
    by_cases hi : isRefund i = true
    · have hi' := congrFun heq i
      simp only [actEmbed, Pi.add_apply, hstate_slot _ _ _ i hi, zero_add] at hi'
      exact hi'
    · have hfalse : isRefund i = false := Bool.eq_false_iff.mpr hi
      simp [hrefund_slot _ i hfalse]
  have hx : x₁ = x₂ := hrefund_inj hrefund_eq
  have hstate_eq : encodeState nf₁ ctx₁ t₁ = encodeState nf₂ ctx₂ t₂ := by
    funext i
    have hi := congrFun heq i
    have hr := congrFun hrefund_eq i
    simp only [actEmbed, Pi.add_apply] at hi
    exact add_right_cancel (hi.trans (congrArg (encodeState nf₂ ctx₂ t₂ i + ·) hr.symm))
  have hp := hstate_inj (a₁ := (nf₁, ctx₁, t₁)) (a₂ := (nf₂, ctx₂, t₂)) hstate_eq
  rcases Prod.mk.inj hp with ⟨rfl, hp'⟩
  rcases Prod.mk.inj hp' with ⟨rfl, rfl⟩
  subst hx
  rfl

/-- Under an injective semantic-message embedding `embed`, any collision of
`UOV.structuredTarget F G (embed ·) ·` across distinct semantic messages `m₁ ≠ m₂` forces
`r₁ ≠ r₂` and `G r₁ = G r₂`. -/
theorem structuredTarget_collision {Message' : Type} [AddCommGroup Message]
    (F : R → Message) (G : R → Tail) (embed : Message' → Message)
    (hembed : Function.Injective embed) {m₁ m₂ : Message'} {r₁ r₂ : R}
    (hm : m₁ ≠ m₂)
    (htarg : UOV.structuredTarget F G (embed m₁) r₁ = UOV.structuredTarget F G (embed m₂) r₂) :
    r₁ ≠ r₂ ∧ G r₁ = G r₂ := by
  have hfst : F r₁ + embed m₁ = F r₂ + embed m₂ := congrArg Prod.fst htarg
  have hsnd : G r₁ = G r₂ := congrArg Prod.snd htarg
  refine ⟨fun hr => hm (hembed (add_left_cancel (a := F r₁) ?_)), hsnd⟩
  simpa [hr] using hfst

/-! ### Reduction proofs and VOLE-ACT-MQ credit conservation (Theorem 3) -/

/-- Transform an `ExtractedForger` execution into the corresponding `clawReduction` execution. -/
private def clawExecutionOfExtracted [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (run : Execution PK Message R Sig) : ClawExecution PK M R Sig :=
  let logged := run.log.foldl (stepValidClaim S J embed run.publicKey) []
  let y := J (embed run.output.payload.message) run.output.payload.opening
  let claims :=
    if S.verify run.publicKey y run.output.signature &&
        !(logged.map fun c => J c.message c.opening).contains y then
      ⟨embed run.output.payload.message, run.output.payload.opening, run.output.signature⟩ :: logged
    else
      []
  ⟨run.publicKey, claims, run.log.map fun (p, sig) => ((embed p.message, p.opening), sig)⟩

private theorem eval_runClaw_clawReduction_eq [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (target : Message → R → Target) (htarget : ∀ m r, target m r = J (embed m) r)
    (B : ExtractedForger PK Message R Sig) :
    ProbComp.eval (runClaw S J (clawReduction S J embed B)) =
      (ProbComp.eval (runExtracted S target B)).map (clawExecutionOfExtracted S J embed) := by
  simp only [runClaw, clawReduction, runExtracted, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.map_bind]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun keys _ => ?_
  rcases keys with ⟨pk, sk⟩
  dsimp only
  let represent :
      List (Payload Message R × Sig) → List (ClawClaim M R Sig) × List ((M × R) × Sig) :=
    fun extLog =>
      (extLog.foldl (stepValidClaim S J embed pk) [],
        extLog.map fun (p, sig) => ((embed p.message, p.opening), sig))
  have hsim :
      (ProbOracleComp.runWith
          (fun payload log =>
            ProbComp.eval ((fun r => (r, log ++ [(payload, r)])) <$>
              S.sign sk (target payload.message payload.opening)))
          (B pk) []).map (fun ⟨token, log⟩ => (token, represent log)) =
        ProbOracleComp.runWith
          (fun payload state =>
            (ProbOracleComp.runWith
              (fun q log =>
                ProbComp.eval ((fun r => (r, log ++ [(q, r)])) <$> S.sign sk (J q.1 q.2)))
              ((clawReductionHandler S J embed pk payload).run state.1) state.2).map
                fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
          (B pk) ([], []) := by
    refine ProbOracleComp.runWith_map_state _ _ represent (fun payload extLog => ?_) (B pk) []
    simp only [clawReductionHandler, StateT.run, ProbComp.eval_map, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, PMF.bind_map, PMF.map_comp,
      PMF.map_bind, htarget]
    congr 1 with sig : 1
    simp [represent, Function.comp_def]
  have hrun :
      ProbComp.eval
          ((((OracleComp.interpret
              (OracleComp.sumHandler
                (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
                (clawReductionHandler S J embed pk))
              (B pk)).run []).runState
            (fun q log => (fun r => (r, log ++ [(q, r)])) <$> S.sign sk (J q.1 q.2))).run []) =
        (ProbComp.eval
            (((B pk).runState fun payload log =>
              (fun r => (r, log ++ [(payload, r)])) <$>
                S.sign sk (target payload.message payload.opening)).run [])).map
          fun ⟨token, extLog⟩ => ((token, (represent extLog).1), (represent extLog).2) := by
    rw [ProbOracleComp.eval_runState, ProbOracleComp.eval_runState]
    rw [ProbOracleComp.runWith_run_interpret
      (clawReductionHandler S J embed pk)
      (fun q log => ProbComp.eval ((fun r => (r, log ++ [(q, r)])) <$> S.sign sk (J q.1 q.2)))
      (B pk) [] []]
    rw [← hsim, PMF.map_comp]
    rfl
  simp only [ProbOracleComp.runLog] at hrun ⊢
  rw [ProbOracleComp.runState_bind, StateT.run_bind, ProbComp.eval_bind, hrun, PMF.bind_map,
    PMF.bind_bind]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨token, extLog⟩ _ => ?_
  dsimp only [Function.comp_def, represent]
  rw [PMF.pure_map]
  dsimp only [clawExecutionOfExtracted]
  split_ifs <;> simp [ProbOracleComp.runState_pure]

private theorem foldl_stepValidClaim_subset [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (pk : PK) (xs : List (Payload Message R × Sig)) (acc : List (ClawClaim M R Sig))
    {c : ClawClaim M R Sig} (hc : c ∈ acc) :
    c ∈ xs.foldl (stepValidClaim S J embed pk) acc := by
  induction xs generalizing acc with
  | nil => exact hc
  | cons x xs ih =>
    apply ih
    simp only [stepValidClaim]
    split_ifs
    · exact List.mem_append_left _ hc
    · exact hc

private theorem stepValidClaim_invariant [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (pk : PK) (entries : List (Payload Message R × Sig))
    (acc : List (ClawClaim M R Sig))
    (hverify : ∀ c ∈ acc, S.verify pk (J c.message c.opening) c.preimage = true)
    (hnodup : (acc.map fun c => J c.message c.opening).Nodup) :
    let res := entries.foldl (stepValidClaim S J embed pk) acc
    (∀ c ∈ res, S.verify pk (J c.message c.opening) c.preimage = true) ∧
      (res.map fun c => J c.message c.opening).Nodup ∧
      (∀ c ∈ res,
        c ∈ acc ∨
          J c.message c.opening ∈ entries.map fun (p, _) => J (embed p.message) p.opening) ∧
      ((∀ e ∈ entries, S.verify pk (J (embed e.1.message) e.1.opening) e.2 = true) →
        ∀ e ∈ entries,
          J (embed e.1.message) e.1.opening ∈ res.map fun c => J c.message c.opening) := by
  induction entries generalizing acc with
  | nil =>
    refine ⟨hverify, hnodup, fun c hc => Or.inl hc, fun _ _ he => absurd he (by simp)⟩
  | cons hd tl ih =>
    let acc' := stepValidClaim S J embed pk acc hd
    have hstep_verify : ∀ c ∈ acc', S.verify pk (J c.message c.opening) c.preimage = true := by
      intro c hc
      simp only [acc', stepValidClaim] at hc
      split_ifs at hc with hcond
      · rcases List.mem_append.mp hc with hc | hc
        · exact hverify c hc
        · obtain rfl := List.mem_singleton.mp hc
          exact (Bool.and_eq_true_iff.mp hcond).1
      · exact hverify c hc
    have hstep_nodup : (acc'.map fun c => J c.message c.opening).Nodup := by
      simp only [acc', stepValidClaim]
      split_ifs with hcond
      · rw [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.mpr ⟨hnodup, List.nodup_singleton _, fun x hx y hy hxy => ?_⟩
        rw [List.mem_singleton.mp hy] at hxy
        subst hxy
        have hnot := (Bool.and_eq_true_iff.mp hcond).2
        simp [hx] at hnot
      · exact hnodup
    obtain ⟨hv_tl, hnd_tl, hmem_tl, hcov_tl⟩ := ih acc' hstep_verify hstep_nodup
    refine ⟨hv_tl, hnd_tl, ?_, ?_⟩
    · intro c hc
      rcases hmem_tl c hc with hc' | hc'
      · simp only [acc', stepValidClaim] at hc'
        split_ifs at hc'
        · rcases List.mem_append.mp hc' with hc' | hc'
          · exact Or.inl hc'
          · right
            rw [List.mem_singleton.mp hc']
            simp
        · exact Or.inl hc'
      · exact Or.inr (List.mem_cons_of_mem _ hc')
    · intro hall e he
      rcases List.mem_cons.mp he with rfl | he_tl
      · have hhd_v : S.verify pk (J (embed e.1.message) e.1.opening) e.2 = true :=
          hall e List.mem_cons_self
        have hhd_in :
            J (embed e.1.message) e.1.opening ∈ acc'.map fun c => J c.message c.opening := by
          simp only [acc', stepValidClaim]
          by_cases hcont : (acc.map fun c => J c.message c.opening).contains
              (J (embed e.1.message) e.1.opening) = true
          · simp only [hhd_v, hcont, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact List.contains_iff_mem.mp hcont
          · have hnot_mem :
                J (embed e.1.message) e.1.opening ∉ acc.map fun c => J c.message c.opening := by
              simpa [List.contains_iff_mem] using hcont
            simp [hhd_v, hnot_mem]
        obtain ⟨c, hc_acc', hc_eq⟩ := List.mem_map.mp hhd_in
        exact List.mem_map.mpr ⟨c, foldl_stepValidClaim_subset S J embed pk tl acc' hc_acc', hc_eq⟩
      · exact hcov_tl (fun e' he' => hall e' (List.mem_cons_of_mem _ he')) e he_tl

private theorem clawAccept_or_binding_or_invalid_of_extractedAccept
    [DecidableEq Message] [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (target : Message → R → Target) (htarget : ∀ m r, target m r = J (embed m) r)
    (run : Execution PK Message R Sig) (h : extractedAccept S target run = true) :
    clawAccept S J (clawExecutionOfExtracted S J embed run) = true ∨
      (findBindingWitness target run.output.payload run.log).any (checkBindingWitness target) =
        true ∨
      anyInvalidReply S target run = true := by
  by_cases hinv : anyInvalidReply S target run = true
  · exact Or.inr (Or.inr hinv)
  · have hvalid_log :
        ∀ e ∈ run.log, S.verify run.publicKey (J (embed e.1.message) e.1.opening) e.2 = true := by
      intro e he
      have hnot : anyInvalidReply S target run = false := Bool.eq_false_iff.mpr hinv
      simp only [anyInvalidReply, List.any_eq_false, Bool.not_eq_true'] at hnot
      rw [← htarget]
      exact Bool.eq_true_of_not_eq_false (hnot e he)
    obtain ⟨hvalid_out, hfresh_raw⟩ := Bool.and_eq_true_iff.mp h
    have hfresh : run.output.payload.message ∉ run.log.map fun (p, _) => p.message :=
      of_decide_eq_true hfresh_raw
    cases hfind : run.log.find? (fun entry => decide
        (target entry.1.message entry.1.opening =
          target run.output.payload.message run.output.payload.opening)) with
    | some entry =>
      right; left
      have hentry := List.mem_of_find?_eq_some hfind
      have hsame := List.find?_some (p := fun entry : Payload Message R × Sig => decide
        (target entry.1.message entry.1.opening =
          target run.output.payload.message run.output.payload.opening)) hfind
      have heq : target entry.1.message entry.1.opening =
          target run.output.payload.message run.output.payload.opening :=
        of_decide_eq_true hsame
      have hne : run.output.payload.message ≠ entry.1.message := by
        intro hm
        exact hfresh (List.mem_map.mpr ⟨entry, hentry, hm.symm⟩)
      simp [findBindingWitness, hfind, checkBindingWitness, hne, heq]
    | none =>
      left
      have hnone := List.find?_eq_none.mp hfind
      have hy_fresh :
          J (embed run.output.payload.message) run.output.payload.opening ∉
            run.log.map fun (p, _) => J (embed p.message) p.opening := by
        intro hmem
        obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
        apply hnone e he
        simp only [decide_eq_true_eq, htarget]
        exact heq
      obtain ⟨hv_logged, hnd_logged, hmem_logged, hcov_logged⟩ :=
        stepValidClaim_invariant S J embed run.publicKey run.log [] (by simp) (by simp)
      set logged := run.log.foldl (stepValidClaim S J embed run.publicKey) []
      set y := J (embed run.output.payload.message) run.output.payload.opening
      have hy_out : S.verify run.publicKey y run.output.signature = true := by
        simpa [Token.valid, htarget, y] using hvalid_out
      have hy_not_mem : y ∉ logged.map fun c => J c.message c.opening := by
        intro hmem
        obtain ⟨c, hc, hce⟩ := List.mem_map.mp hmem
        rcases hmem_logged c hc with hc | hc
        · simp at hc
        · exact hy_fresh (hce ▸ hc)
      have hy_not_logged : !(logged.map fun c => J c.message c.opening).contains y = true := by
        simp [hy_not_mem]
      have hclaims_eq :
          (clawExecutionOfExtracted S J embed run).claims =
            ⟨embed run.output.payload.message, run.output.payload.opening, run.output.signature⟩ ::
              logged := by
        dsimp only [clawExecutionOfExtracted]
        split_ifs with hif
        · rfl
        · exfalso
          exact hif (Bool.and_eq_true_iff.mpr ⟨hy_out, hy_not_logged⟩)
      have hsub_len :
          ((run.log.map fun (p, _) => J (embed p.message) p.opening)).dedup.length ≤
            (logged.map fun c => J c.message c.opening).length := by
        refine (List.subperm_of_subset (List.nodup_dedup _) fun t ht => ?_).length_le
        rw [List.mem_dedup, List.mem_map] at ht
        obtain ⟨e, he, rfl⟩ := ht
        exact hcov_logged hvalid_log e he
      have hlt :
          ((clawExecutionOfExtracted S J embed run).log.map fun (q, _) => J q.1 q.2).dedup.length <
            (clawExecutionOfExtracted S J embed run).claims.length := by
        rw [hclaims_eq]
        simp only [clawExecutionOfExtracted, List.map_map, Function.comp_def, List.length_cons]
        simp only [List.length_map] at hsub_len
        omega
      have hnd_claims :
          ((clawExecutionOfExtracted S J embed run).claims.map
            fun c => J c.message c.opening).Nodup := by
        rw [hclaims_eq, List.map_cons, List.nodup_cons]
        exact ⟨hy_not_mem, hnd_logged⟩
      have hv_claims :
          (clawExecutionOfExtracted S J embed run).claims.all
            (fun c => S.verify (clawExecutionOfExtracted S J embed run).publicKey
              (J c.message c.opening) c.preimage) = true := by
        rw [hclaims_eq, List.all_cons, Bool.and_eq_true]
        refine ⟨hy_out, List.all_eq_true.mpr fun c hc => hv_logged c hc⟩
      simp only [clawAccept, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hlt, hnd_claims⟩, hv_claims⟩

/-- Concrete bound decomposing `AnonymousToken.extractedExperiment` into structured-target one-more
claw-freeness (`clawExperiment`), target binding collisions (`bindingExperiment`), and invalid
oracle replies (`invalidReplyExperiment`). -/
theorem extractedExperiment_succProbability_le_claw_add_binding
    [DecidableEq Message] [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (J : M → R → Target) (embed : Message → M)
    (target : Message → R → Target) (htarget : ∀ m r, target m r = J (embed m) r)
    (B : ExtractedForger PK Message R Sig) :
    Experiment.succProbability (extractedExperiment S target B) ≤
      Experiment.succProbability (clawExperiment S J (clawReduction S J embed B)) +
        Experiment.succProbability (bindingExperiment S target B) +
        Experiment.succProbability (invalidReplyExperiment S target B) := by
  simp only [Experiment.succProbability, extractedExperiment, clawExperiment, bindingExperiment,
    bindingReduction, invalidReplyExperiment, ProbComp.eval_map,
    eval_runClaw_clawReduction_eq S J embed target htarget, PMF.map_comp, Function.comp_def,
    Game.succProbability]
  rw [← ENNReal.toNNReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    ← ENNReal.toNNReal_add (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩)
      (PMF.apply_ne_top _ _)]
  apply ENNReal.toNNReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩, PMF.apply_ne_top _ _⟩)
  let μ := ProbComp.eval (runExtracted S target B)
  have hsplit1 :
      (μ.map (extractedAccept S target)) true ≤
        (μ.map fun run => clawAccept S J (clawExecutionOfExtracted S J embed run)) true +
          (μ.map fun run =>
            (findBindingWitness target run.output.payload run.log).any
              (checkBindingWitness target) || anyInvalidReply S target run) true := by
    refine Cslib.Probability.PMF.map_true_le_add μ fun run _ h => ?_
    rcases clawAccept_or_binding_or_invalid_of_extractedAccept S J embed target htarget run h with
      hc | hb | hi
    · exact Or.inl hc
    · exact Or.inr (Bool.or_eq_true_iff.mpr (Or.inl hb))
    · exact Or.inr (Bool.or_eq_true_iff.mpr (Or.inr hi))
  have hsplit2 :
      (μ.map fun run =>
          (findBindingWitness target run.output.payload run.log).any (checkBindingWitness target) ||
            anyInvalidReply S target run) true ≤
        (μ.map fun run =>
          (findBindingWitness target run.output.payload run.log).any
            (checkBindingWitness target)) true +
          (μ.map (anyInvalidReply S target)) true :=
    Cslib.Probability.PMF.map_true_le_add μ fun _ _ h => Bool.or_eq_true_iff.mp h
  exact (hsplit1.trans (add_le_add le_rfl hsplit2)).trans_eq (add_assoc _ _ _).symm

/-- Under an injective semantic-message embedding `embed` into `UOV.structuredTarget F G`, target
binding collisions reduce to `G`-collisions in `R`. -/
theorem bindingExperiment_structuredTarget_le_gCollision
    {Message' : Type} [DecidableEq Message'] [DecidableEq Message] [DecidableEq R]
    [DecidableEq Tail] [AddCommGroup Message]
    (F : R → Message) (G : R → Tail) (embed : Message' → Message)
    (hembed : Function.Injective embed)
    (target : Message' → R → Message × Tail)
    (htarget : ∀ m r, target m r = UOV.structuredTarget F G (embed m) r)
    (S : Signature.Scheme PK SK (Message × Tail) Sig)
    (B : ExtractedForger PK Message' R Sig) :
    Experiment.succProbability (bindingExperiment S target B) ≤
      Experiment.succProbability (gCollisionExperiment G (gCollisionReduction S target B)) := by
  simp only [Experiment.succProbability, bindingExperiment, gCollisionExperiment,
    gCollisionReduction, ProbComp.eval_map, PMF.map_comp, Function.comp_def, Game.succProbability]
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  refine Cslib.Probability.PMF.map_true_mono _ fun opt _ hopt => ?_
  cases opt with
  | none => simp at hopt
  | some w =>
    simp only [Option.any_some, checkBindingWitness, decide_eq_true_eq, htarget] at hopt
    have hcol := structuredTarget_collision F G embed hembed hopt.1 hopt.2
    simp [gCollisionAccept, hcol.1, hcol.2]

/-- Concrete bound decomposing `AnonymousToken.extractedExperiment` against
`UOV.structuredTarget F G (embed ·) ·` into structured-target one-more claw-freeness, a `G`-block
collision, and issuer oracle reply invalidity. -/
theorem extractedExperiment_succProbability_le_structuredClaw
    {Message' : Type} [DecidableEq Message'] [DecidableEq Message] [DecidableEq R]
    [DecidableEq Tail] [AddCommGroup Message]
    (F : R → Message) (G : R → Tail) (embed : Message' → Message)
    (hembed : Function.Injective embed)
    (target : Message' → R → Message × Tail)
    (htarget : ∀ m r, target m r = UOV.structuredTarget F G (embed m) r)
    (S : Signature.Scheme PK SK (Message × Tail) Sig)
    (B : ExtractedForger PK Message' R Sig) :
    Experiment.succProbability (extractedExperiment S target B) ≤
      Experiment.succProbability
          (clawExperiment S (UOV.structuredTarget F G)
            (clawReduction S (UOV.structuredTarget F G) embed B)) +
        Experiment.succProbability (gCollisionExperiment G (gCollisionReduction S target B)) +
        Experiment.succProbability (invalidReplyExperiment S target B) := by
  have h1 := extractedExperiment_succProbability_le_claw_add_binding
    S (UOV.structuredTarget F G) embed target htarget B
  have h2 := bindingExperiment_structuredTarget_le_gCollision F G embed hembed target htarget S B
  exact h1.trans (add_le_add (add_le_add le_rfl h2) le_rfl)

/-- **Theorem 3 (Extracted VOLE-ACT-MQ credit conservation).** Under an injective embedding
`actEmbed encodeState refundEmbed`, any adversary winning the extracted VOLE-ACT credit-conservation
game against `(actCom F G encodeState, actTag refundEmbed, S)` either yields a win in the
structured-target one-more claw-freeness game via `clawReduction … (noteForger … A)`, yields a
`G`-collision via `gCollisionReduction`, or encounters an invalid issuer reply (probability zero
when `S.Correct` holds). -/
theorem actMQConservation_succProbability_le
    {Nullifier Context : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Message] [DecidableEq Tail]
    [DecidableEq R] [AddCommGroup Message]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited R] [Inhabited Sig]
    (F : R → Message) (G : R → Tail)
    (encodeState : Nullifier → Context → ℕ → Message) (refundEmbed : ℕ → Message)
    (hembed : Function.Injective (actEmbed encodeState refundEmbed))
    (S : Signature.Scheme PK SK (Message × Tail) Sig)
    (A : Conservation.ExtractedAdversary Nullifier Context R (Message × Tail) PK Sig) :
    Experiment.succProbability
        (Conservation.extractedConservationExperiment (actCom F G encodeState) (actTag refundEmbed)
          S A) ≤
      Experiment.succProbability
          (clawExperiment S (UOV.structuredTarget F G)
            (clawReduction S (UOV.structuredTarget F G) (actEmbed encodeState refundEmbed)
              (Conservation.noteForger (actCom F G encodeState) (actTag refundEmbed) S A))) +
        Experiment.succProbability
          (gCollisionExperiment G
            (gCollisionReduction S (Credit.target (actCom F G encodeState) (actTag refundEmbed))
              (Conservation.noteForger (actCom F G encodeState) (actTag refundEmbed) S A))) +
        Experiment.succProbability
          (invalidReplyExperiment S (Credit.target (actCom F G encodeState) (actTag refundEmbed))
            (Conservation.noteForger (actCom F G encodeState) (actTag refundEmbed) S A)) := by
  refine (Conservation.extractedConservationExperiment_succProbability_le_extractedExperiment
    (actCom F G encodeState) (actTag refundEmbed) S A).trans ?_
  exact extractedExperiment_succProbability_le_structuredClaw F G
    (actEmbed encodeState refundEmbed) hembed
    (Credit.target (actCom F G encodeState) (actTag refundEmbed))
    (credit_target_actCom_actTag F G encodeState refundEmbed) S
    (Conservation.noteForger (actCom F G encodeState) (actTag refundEmbed) S A)

/-- The composed ACT-MQ claw reduction preserves a `q`-query bound from the extracted
credit-conservation adversary `A`. -/
theorem actMQClawReduction_queryBound
    {Nullifier Context : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Message] [DecidableEq Tail]
    [AddCommGroup Message]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited R] [Inhabited Sig]
    (F : R → Message) (G : R → Tail)
    (encodeState : Nullifier → Context → ℕ → Message) (refundEmbed : ℕ → Message)
    (S : Signature.Scheme PK SK (Message × Tail) Sig)
    (A : Conservation.ExtractedAdversary Nullifier Context R (Message × Tail) PK Sig)
    (pk : PK) {q : ℕ} (hA : (A pk).IsQueryBounded q) :
    (clawReduction S (UOV.structuredTarget F G) (actEmbed encodeState refundEmbed)
      (Conservation.noteForger (actCom F G encodeState) (actTag refundEmbed) S A)
        pk).IsQueryBounded q :=
  clawReduction_queryBound S (UOV.structuredTarget F G) (actEmbed encodeState refundEmbed)
    (Conservation.noteForger (actCom F G encodeState) (actTag refundEmbed) S A) pk
    (Conservation.noteForger_queryBound (actCom F G encodeState) (actTag refundEmbed) S A pk hA)

end

end Cslib.Crypto.AnonymousToken.ACTMQ
