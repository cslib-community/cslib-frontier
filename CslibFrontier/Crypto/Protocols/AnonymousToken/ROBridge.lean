/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.AnonymousToken.Basic
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
public import CslibFrontier.Crypto.Protocols.VOLE.ROExtractor
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunLog
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Map

/-!
# Straight-line VOLEitH ROM bridges to `AnonymousToken`

This module composes straight-line `leaf_hash::shake` VOLE-in-the-head ROM extraction
(`Cslib.Crypto.Protocols.VOLE.ROExtractor`) with `AnonymousToken.Basic` and
`AnonymousToken.Conservation`:

* **`AnonymousToken.Basic` bridge**: unextracted ROM token-unforgeability adversaries against
  proof-gated signing (`romUnextractedTokenExperiment`) reduce straight-line via
  `extractedForgerOfROM` to `AnonymousToken.extractedExperiment` with additive error
  `voleithKSBound` (`unextractedTokenExperiment_succProbability_le_extracted`) and to EUF-CMA +
  target binding + `voleithKSBound` (`unextractedTokenExperiment_succProbability_le`).
* **`AnonymousToken.Conservation` bridge**: unextracted ROM credit-conservation adversaries against
  a VOLEitH-checked single-issuer oracle (`romUnextractedConservationExperiment`) reduce
  straight-line via `extractedAdversaryOfROM` to `Conservation.extractedConservationExperiment`
  (`unextractedConservationExperiment_succProbability_le_extracted`) and to EUF-CMA + commitment
  binding + `voleithKSBound` (`unextractedConservationExperiment_succProbability_le_prod_mk`).

Because a single-issuer VOLE-ACT/token server only verifies client proofs (`Issue`, `Spend`, token
certification) and never simulates proofs for the adversary ([VOLEACT2026]; specializing
[BaumBMRS2023Eprint], Lemma 4, pp. 19–20, to a single challenge repetition `µ = 1`), plain
straight-line multi-verify ROM extraction suffices without simulation-extractability.

## Main definitions

* `ROMTokenRequest`, `romTokenRel`, `ROMTokenSpec`, `ROMTokenExecution`, `romTokenAccept`,
  `runROMUnextractedToken`, `romUnextractedTokenExperiment`, `extractedForgerOfROM`: unextracted
  ROM anonymous-token game and straight-line `ExtractedForger` reduction.
* `ROMIssueStatement`, `ROMSpendStatement`, `ROMConservationQuery`, `ROMConservationStmt`,
  `ROMIssueWitness`, `ROMSpendWitness`, `ROMConservationWitness`, `ROMConservationRequest`,
  `romConservationRel`, `ROMConservationSpec`, `ROMConservationExecution`,
  `romConservationAccept`, `runROMUnextractedConservation`, `romUnextractedConservationExperiment`,
  `extractedAdversaryOfROM`: unextracted ROM credit-conservation game and straight-line
  `Conservation.ExtractedAdversary` reduction.

## Main results

* `extractedForgerOfROM_isQueryBounded`, `unextractedTokenExperiment_succProbability_le_extracted`,
  `unextractedTokenExperiment_succProbability_le`: query-budget preservation and concrete
  ROM-to-extracted and EUF-CMA + binding security bounds for `AnonymousToken.Basic`.
* `extractedAdversaryOfROM_isQueryBounded`,
  `unextractedConservationExperiment_succProbability_le_extracted`,
  `unextractedConservationExperiment_succProbability_le_prod_mk`: query-budget preservation and
  concrete ROM-to-extracted and EUF-CMA + commitment-binding security bounds for
  `AnonymousToken.Conservation`.

## Scope and gaps

* Bounded conditional single-repetition bridges toward #7068 (#4987): inherit the
  `VOLEITHSoundnessError` (`ε_rel`) premise from `VOLE.ROExtractor` and the single-issuer extracted
  game modeling choices from `AnonymousToken.Basic` and `AnonymousToken.Conservation`; all bounds
  are query-bounded `ProbComp`/`ProbOracleComp` reductions rather than PPT/`TimeM` certificates.

## References

* [C. Baum et al., *Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from
  VOLE-in-the-Head* (full version, ePrint 2023/996)][BaumBMRS2023Eprint], Section 4 (Lemma 4,
  pp. 19–20).
* [T. Zhang, C. Patton, S. Schlesinger, *VOLE-ACT*][VOLEACT2026], Parameters, Tag, Initial Issuance,
  and Spending.
-/

public section

namespace Cslib.Crypto.AnonymousToken

open Cslib Cslib.Probability Cslib.OracleComp Cslib.Crypto.Protocols.VOLE
open scoped ENNReal NNReal
private theorem isCostBounded_sample_bind_pure_zero {ι α β : Type} (spec : OracleSpec ι)
    {outCost : ι → ℕ} (m : ProbComp α) (f : α → β) :
    IsCostBounded (Sum.elim (fun _ => 0) outCost)
      (ProbOracleComp.sample (spec := spec) m >>= fun x => pure (f x)) 0 :=
  ((ProbOracleComp.isCostBounded_sample _ m).bind fun x =>
    OracleComp.IsCostBounded.pure (f x) 0).mono (Nat.zero_le 0)

private theorem run_interpret_sumUnif_isCostBounded
    {ιReq ιRO : Type} {ReqSpec : ιReq → Type} {ROSpec : ιRO → Type}
    {ιOut : Type} {OutSpec : ιOut → Type} {S α : Type}
    (inner : (q : ιReq ⊕ ιRO) → StateT S (ProbOracleComp OutSpec) ((ReqSpec ⊕ₒ ROSpec) q))
    (reqCost : ιReq → ℕ) (roCost : ιRO → ℕ) (outCost : ιOut → ℕ)
    (hReq : ∀ req (s : S), IsCostBounded (Sum.elim (fun _ => 0) outCost)
      ((inner (.inl req)).run s) (reqCost req))
    (hRO : ∀ qRO (s : S), IsCostBounded (Sum.elim (fun _ => 0) outCost)
      ((inner (.inr qRO)).run s) (roCost qRO))
    (prog : ProbOracleComp ((ReqSpec ⊕ₒ ROSpec)) α) (s₀ : S) {B : ℕ}
    (hB : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim reqCost roCost)) prog B) :
    IsCostBounded (Sum.elim (fun _ => 0) outCost)
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          inner)
        prog).run s₀) B := by
  refine OracleComp.IsCostBounded.run_interpret
    (cost := Sum.elim (fun _ => 0) (Sum.elim reqCost roCost))
    (cost' := Sum.elim (fun _ => 0) outCost) ?_ hB s₀
  intro q s
  rcases q with n | (req | qRO)
  · simpa only [StateT.run_lift, Sum.elim_inl] using
      isCostBounded_sample_bind_pure_zero OutSpec (ProbComp.unifFin n) fun a => (a, s)
  · exact hReq req s
  · exact hRO qRO s

private theorem isCostBounded_sample_ite_query {ι R S : Type} {spec : OracleSpec ι}
    (m : ProbComp (Bool × S)) (q : ι) (f : S → spec q → R × S) (g : S → R × S) :
    IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1))
      (ProbOracleComp.sample m >>= fun (ok, s') =>
        if ok then ProbOracleComp.query q >>= fun r => pure (f s' r) else pure (g s')) 1 := by
  change IsCostBounded _ _ (0 + 1)
  refine (ProbOracleComp.isCostBounded_sample _ m).bind fun (ok, s') => ?_
  cases ok
  · exact OracleComp.IsCostBounded.pure _ 1
  · change IsCostBounded _ (ProbOracleComp.query q >>= fun r => pure (f s' r)) (1 + 0)
    exact (OracleComp.IsCostBounded.query (spec := probOracleSpec _) (Sum.inr q)).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0


private theorem bind_tsum_add_voleithKSBound_toNNReal {Keys : Type}
    (romGame extGame : Experiment)
    (keyDist : PMF Keys) (lhs rhs : Keys → PMF Bool) (bound : ℝ≥0)
    (hkey_le : ∀ k, (lhs k) true ≤ (rhs k) true + (bound : ℝ≥0∞))
    (hlhs : ProbComp.eval romGame = keyDist.bind lhs)
    (hrhs : ProbComp.eval extGame = keyDist.bind rhs) :
    romGame.succProbability ≤ extGame.succProbability + bound := by
  have hprob_le :
      ProbComp.eval romGame true ≤ ProbComp.eval extGame true + (bound : ℝ≥0∞) := by
    rw [hlhs, hrhs, PMF.bind_apply, PMF.bind_apply]
    calc
      (∑' k, keyDist k * (lhs k) true)
        ≤ ∑' k, keyDist k * ((rhs k) true + (bound : ℝ≥0∞)) := by
          refine tsum_le_tsum fun k => ?_
          gcongr
          exact hkey_le k
      _ = (∑' k, keyDist k * (rhs k) true) + ∑' k, keyDist k * (bound : ℝ≥0∞) := by
          simp_rw [mul_add]
          rw [tsum_add]
      _ = _ := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hnn := ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, ENNReal.coe_ne_top⟩) hprob_le
  rw [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe] at hnn
  exact hnn


private theorem eval_runState_voleithMemoizeProg {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (prog : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α)
    (roSt : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) :
    ProbComp.eval ((ProbOracleComp.runState prog voleithMemoizeProg) roSt) =
      ProbOracleComp.runWith voleithMemoize prog roSt := by
  change ProbComp.eval ((ProbOracleComp.runState prog voleithMemoizeProg).run roSt) = _
  rw [ProbOracleComp.eval_runState]
  exact congrArg (ProbOracleComp.runWith · prog roSt) (funext₂ eval_voleithMemoizeProg)

/-! ### Bridge to `AnonymousToken.Basic` -/

section AnonymousTokenBridge

/-- Client signing request in the unextracted `leaf_hash::shake` ROM anonymous-token game: the
client asks the signer to certify a public `target` while proving knowledge of an opening via a
VOLEitH proof `proof`. -/
structure ROMTokenRequest (Message Target : Type) (d comLen rowLen : ℕ)
    (Seed IV PreMsg : Type) where
  /-- Semantic message bound into the token payload. -/
  message : Message
  /-- Blinded / committed target submitted to the signer. -/
  target : Target
  /-- Straight-line extractable VOLEitH proof for `(message, target)`. -/
  proof : VOLEITHProof d comLen rowLen Seed IV PreMsg
  deriving DecidableEq

/-- Public VOLEitH statement `(req.message, req.target)` proven by `ROMTokenRequest`. -/
@[expose] def ROMTokenRequest.stmt {Message Target : Type} {d comLen rowLen : ℕ}
    {Seed IV PreMsg : Type} (req : ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg) :
    Message × Target :=
  (req.message, req.target)

/-- Relation verified in the ROM anonymous-token signing request: `targetFn msg open_ = target`. -/
@[expose] def romTokenRel {Message Opening Target : Type} [DecidableEq Target]
    (targetFn : Message → Opening → Target)
    (stmt : Message × Target) (open_ : Opening) : Bool :=
  decide (targetFn stmt.1 open_ = stmt.2)

/-- Signing oracle specification returning `some sig` on proof acceptance and `none` otherwise. -/
abbrev ROMTokenSignSpec (Message Target : Type) (d comLen rowLen : ℕ)
    (Seed IV PreMsg Sig : Type) :
    OracleSpec (ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg) :=
  fun _ => Option Sig

/-- Combined oracle specification exposed to an unextracted ROM token adversary. -/
abbrev ROMTokenSpec (Message Target : Type) (d sdLen comLen rowLen : ℕ)
    (Seed IV PreMsg Chal Sig : Type) :=
  ROMTokenSignSpec Message Target d comLen rowLen Seed IV PreMsg Sig ⊕ₒ
    VOLEITHROSpec d sdLen comLen rowLen (Message × Target) Seed IV PreMsg Chal

/-- Transcript of an unextracted ROM anonymous-token adversary execution. -/
structure ROMTokenExecution (PK Message Opening Sig : Type) where
  /-- Signer public verification key. -/
  publicKey : PK
  /-- Final forged token emitted by the adversary. -/
  output : Token Message Opening Sig
  /-- Messages signed after VOLEitH proof verification succeeded. -/
  signedMessages : List Message

/-- Winning condition for the unextracted ROM token adversary: valid token on a fresh message. -/
@[expose] def romTokenAccept {PK SK Message Opening Target Sig : Type} [DecidableEq Message]
    (S : Signature.Scheme PK SK Target Sig) (targetFn : Message → Opening → Target)
    (run : ROMTokenExecution PK Message Opening Sig) : Bool :=
  Token.valid S targetFn run.publicKey run.output &&
    decide (run.output.payload.message ∉ run.signedMessages)

/-- Acceptance continuation for `ROMTokenSpec` that signs `req.target` and appends `req.message`
to `signedMessages`. -/
@[expose] noncomputable def romTokenAcceptReal {d comLen rowLen : ℕ}
    {PK SK Message Target Seed IV PreMsg Sig : Type}
    (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (req : ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg)
    (msgs : List Message) : ProbComp (Option Sig × List Message) :=
  (S.sign keys.2 req.target).map fun sig => (some sig, msgs ++ [req.message])

/-- Execute an unextracted ROM token adversary against the verifier-checked signing oracle and lazy
two-channel ROM. -/
@[expose] noncomputable def runROMUnextractedToken {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    (S : Signature.Scheme PK SK Target Sig)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig)) :
    ProbComp (ROMTokenExecution PK Message Opening Sig) := do
  let keys ← S.keyGen
  let ⟨output, _, signedMessages⟩ ←
    ((A keys.1).runState (verifyGatedHandlerProg (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx ROMTokenRequest.stmt ROMTokenRequest.proof checkRel none
      (romTokenAcceptReal S keys))).run (([], []), [])
  pure { publicKey := keys.1, output := output, signedMessages := signedMessages }

/-- Unextracted ROM anonymous-token unforgeability game, original to this library (note that
`ROMTokenRequest.message` is sent publicly in the clear and logged against `signedMessages`,
modeling declared-message token issuance rather than blind issuance / OMUF). -/
@[expose] noncomputable def romUnextractedTokenExperiment {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Message]
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    (S : Signature.Scheme PK SK Target Sig) (targetFn : Message → Opening → Target)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig)) : Experiment :=
  romTokenAccept S targetFn <$>
    runROMUnextractedToken expand chalToIdx checkRel S A

private noncomputable def romToExtractedInner {d sdLen comLen rowLen : ℕ}
    {Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool) :
    (q : ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg ⊕
      (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen (Message × Target) IV PreMsg)) →
      StateT (VOLEITHTraceState d sdLen comLen rowLen (Message × Target) Seed IV PreMsg Chal)
        (ProbOracleComp (fun _ : Payload Message Opening => Sig))
        (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg Chal Sig q)
  | .inl req, roSt => do
    let (ok, roSt') ← ProbOracleComp.sample ((ProbOracleComp.runState
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel req.stmt req.proof)
      voleithMemoizeProg).run roSt)
    if ok then
      let openStar := extractWitnessFromTrace expand decWit roSt.1 req.proof
      let sig ← ProbOracleComp.query ⟨req.message, openStar⟩
      pure (some sig, roSt')
    else
      pure (none, roSt')
  | .inr qRO, roSt => do
    let (ans, roSt') ← ProbOracleComp.sample ((voleithMemoizeProg qRO).run roSt)
    pure (ans, roSt')

/-- Straight-line extracted-model `ExtractedForger` constructed from an unextracted ROM adversary
`A`: simulates `VOLEITHROSpec` locally, checks `voleithVerifyROM`, and whenever a request
verifies, extracts `open* = extractWitnessFromTrace tr_leaf prf` without rewinding and forwards
`⟨req.message, open*⟩` to the `ExtractedForger` signing oracle. -/
noncomputable def extractedForgerOfROM {d sdLen comLen rowLen : ℕ}
    {PK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig)) :
    ExtractedForger PK Message Opening Sig := fun pk =>
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (romToExtractedInner expand decWit chalToIdx checkRel))
    (A pk)).run ([], [])

/-- `extractedForgerOfROM` preserves signing-query budgets: every `VOLEITHROSpec` call costs `0`
signing queries and every signing request calls the extracted signing oracle at most once. -/
theorem extractedForgerOfROM_isQueryBounded {d sdLen comLen rowLen : ℕ}
    {PK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig))
    {m : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m) :
    ∀ pk, (extractedForgerOfROM expand decWit chalToIdx checkRel A pk).IsQueryBounded m := by
  intro pk
  unfold extractedForgerOfROM
  rw [ProbOracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
  refine run_interpret_sumUnif_isCostBounded
    (romToExtractedInner expand decWit chalToIdx checkRel)
    (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun req roSt => ?_) (fun qRO roSt => ?_)
    (A pk) ([], []) (hm pk)
  · simpa only [StateT.run, romToExtractedInner] using
      isCostBounded_sample_ite_query
        (spec := fun _ : Payload Message Opening => Sig) (R := Option Sig)
        ((ProbOracleComp.runState
          (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel req.stmt req.proof)
          voleithMemoizeProg).run roSt)
        ⟨req.message, extractWitnessFromTrace expand decWit roSt.1 req.proof⟩
        (fun roSt' sig => (some sig, roSt')) (fun roSt' => (none, roSt'))
  · simpa only [StateT.run, romToExtractedInner] using
      isCostBounded_sample_bind_pure_zero _ _ _

private noncomputable def romTokenAcceptExt {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Sig : Type}
    [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (targetFn : Message → Opening → Target)
    (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (tr₁ : LeafTrace d sdLen comLen Seed IV)
    (req : ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg)
    (msgs : List Message) : ProbComp (Option Sig × List Message) :=
  let openStar := extractWitnessFromTrace expand decWit tr₁ req.proof
  (S.sign keys.2 (targetFn req.message openStar)).map fun sig =>
    (some sig, msgs ++ [req.message])

/-- Concrete query-bounded advantage bound (not an asymptotic PPT security theorem):
any unextracted ROM adversary making at most `m` signing queries, `Q_leaf` leaf queries, and
`Q_FS` Fiat–Shamir queries reduces straight-line (no rewinding) to the extracted-model adversary
`extractedForgerOfROM ... A` with additive loss `voleithKSBound` in `Game.succProbability`. -/
theorem unextractedTokenExperiment_succProbability_le_extracted {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Message] [DecidableEq Target]
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d)) (S : Signature.Scheme PK SK Target Sig)
    (targetFn : Message → Opening → Target)
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx (romTokenRel targetFn) checkRel ε_rel)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig))
    {m Q_leaf Q_FS : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m)
    (hleaf : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) (A pk) Q_leaf)
    (hfs : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) (A pk) Q_FS) :
    (romUnextractedTokenExperiment expand chalToIdx checkRel S targetFn A).succProbability ≤
      (extractedExperiment S targetFn
        (extractedForgerOfROM expand decWit chalToIdx checkRel A)).succProbability +
        voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel := by
  let extH := fun keys : PK × SK =>
    verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx ROMTokenRequest.stmt ROMTokenRequest.proof checkRel (none : Option Sig)
      (romTokenAcceptExt expand decWit targetFn S keys)
  let romH := fun keys : PK × SK =>
    verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx ROMTokenRequest.stmt ROMTokenRequest.proof checkRel (none : Option Sig)
      (fun _ => romTokenAcceptReal S keys)
  have hrom_eval :
      ProbComp.eval (romUnextractedTokenExperiment expand chalToIdx checkRel S targetFn A) =
        (ProbComp.eval S.keyGen).bind fun keys =>
          (ProbOracleComp.runWith (romH keys) (A keys.1) (([], []), [])).map
            fun (tok, (_, msgs)) =>
              Token.valid S targetFn keys.1 tok && decide (tok.payload.message ∉ msgs) := by
    simp only [romUnextractedTokenExperiment, runROMUnextractedToken, ProbComp.eval_map,
      ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_runState, PMF.map_bind]
    congr 1 with keys : 1
    simp only [romH, verifyGatedHandlerProg_eval, PMF.map, Function.comp_def, PMF.pure_bind,
      romTokenAccept]
  have hext_eval :
      ProbComp.eval (extractedExperiment S targetFn
        (extractedForgerOfROM expand decWit chalToIdx checkRel A)) =
        (ProbComp.eval S.keyGen).bind fun keys =>
          (ProbOracleComp.runWith (extH keys) (A keys.1) (([], []), [])).map
            fun (tok, (_, msgs)) =>
              Token.valid S targetFn keys.1 tok && decide (tok.payload.message ∉ msgs) := by
    simp only [extractedExperiment, runExtracted, extractedForgerOfROM, ProbComp.eval_map,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.map, PMF.bind_bind, Function.comp_def,
      PMF.pure_bind]
    congr 1 with keys : 1
    let signO : Payload Message Opening → ProbComp Sig := fun p =>
      S.sign keys.2 (targetFn p.message p.opening)
    let signH : Payload Message Opening → StateT (List (Payload Message Opening × Sig)) PMF Sig :=
      fun p log => (ProbComp.eval (signO p)).map fun sig => (sig, log ++ [(p, sig)])
    let extRun := (OracleComp.interpret
      (OracleComp.sumHandler
        (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (romToExtractedInner expand decWit chalToIdx checkRel))
      (A keys.1)).run ([], [])
    have hlog_map :
        ProbComp.eval ((Prod.fst <$> extRun).runLog signO) =
          (ProbOracleComp.runWith signH extRun []).map (Prod.map Prod.fst id) := by
      simp only [ProbOracleComp.runLog, ProbOracleComp.runState_map, StateT.run_map,
        ProbOracleComp.eval_runState, ProbComp.eval_map]
      congr 2
    erw [hlog_map]
    have hrun := ProbOracleComp.runWith_run_interpret
      (romToExtractedInner expand decWit chalToIdx checkRel) signH (A keys.1) ([], []) []
    let repMsg : VOLEITHTraceState d sdLen comLen rowLen (Message × Target) Seed IV PreMsg Chal ×
        List (Payload Message Opening × Sig) →
        VOLEITHTraceState d sdLen comLen rowLen (Message × Target) Seed IV PreMsg Chal ×
          List Message :=
      fun (roSt, log) => (roSt, log.map fun e => e.1.message)
    have hjoint_eq :
        ((ProbOracleComp.runWith
            (fun q state =>
              PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
                (ProbOracleComp.runWith signH
                  ((romToExtractedInner expand decWit chalToIdx checkRel q).run state.1)
                  state.2))
            (A keys.1) (([], []), [])).map (Prod.map id repMsg)) =
          ProbOracleComp.runWith (extH keys) (A keys.1) (([], []), []) := by
      refine ProbOracleComp.runWith_map_state _ _ repMsg (fun q x => ?_)
        (A keys.1) (([], []), [])
      rcases x with ⟨roSt, log⟩
      rcases q with req | qRO
      · simp only [romToExtractedInner, StateT.run, ProbOracleComp.runWith_bind,
          ProbOracleComp.runWith_sample, extH, verifyGatedHandler,
          eval_runState_voleithMemoizeProg, PMF.map, PMF.bind_bind, Function.comp_def,
          PMF.pure_bind]
        congr 1 with ⟨ok, roSt'⟩ : 1
        cases ok
        · simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure, PMF.pure_bind,
            repMsg]
        · simp only [↓reduceIte, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
            ProbOracleComp.runWith_pure, signH, signO, romTokenAcceptExt, ProbComp.eval_freeMMap,
            PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind, repMsg,
            List.map_append, List.map_cons, List.map_nil]
      · simp only [romToExtractedInner, StateT.run, ProbOracleComp.runWith_bind,
          ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure, repMsg, extH,
          verifyGatedHandler, PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind,
          eval_voleithMemoizeProg]
    rw [hrun, ← hjoint_eq]
    simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind, extractedAccept,
      repMsg, Prod.map]
    rfl
  exact bind_tsum_add_voleithKSBound_toNNReal _ _ (ProbComp.eval S.keyGen) _ _ _
    (fun keys => toOuterMeasure_runWith_verifyGatedHandler_le expand decWit chalToIdx
      (romTokenRel targetFn) ROMTokenRequest.stmt ROMTokenRequest.proof checkRel hSound none
      (romTokenAcceptReal S keys) (romTokenAcceptExt expand decWit targetFn S keys)
      (fun tr req _ hrel => by
        simp [romTokenAcceptReal, romTokenAcceptExt,
          of_decide_eq_true (p := targetFn req.message _ = req.target) hrel])
      [] (A keys.1) (hm keys.1) (hleaf keys.1) (hfs keys.1)
      (fun (tok, (_, msgs)) =>
        Token.valid S targetFn keys.1 tok && decide (tok.payload.message ∉ msgs)))
    hrom_eval hext_eval

/-- Concrete query-bounded advantage bound (not an asymptotic PPT security theorem):
end-to-end ROM reduction for `AnonymousToken.Basic` composing straight-line leaf extraction
with `AnonymousToken.extracted_succProbability_le` to bound an unextracted ROM adversary's forgery
probability by EUF-CMA + target binding + `voleithKSBound`. -/
theorem unextractedTokenExperiment_succProbability_le {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Message] [DecidableEq Target] [Inhabited Sig]
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d)) (S : Signature.Scheme PK SK Target Sig)
    (targetFn : Message → Opening → Target)
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx (romTokenRel targetFn) checkRel ε_rel)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig))
    {m Q_leaf Q_FS : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m)
    (hleaf : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) (A pk) Q_leaf)
    (hfs : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) (A pk) Q_FS) :
    (romUnextractedTokenExperiment expand chalToIdx checkRel S targetFn A).succProbability ≤
      (S.eufCmaExperiment (targetForger targetFn
          (extractedForgerOfROM expand decWit chalToIdx checkRel A))).succProbability +
        (bindingExperiment S targetFn
          (extractedForgerOfROM expand decWit chalToIdx checkRel A)).succProbability +
        voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel := by
  refine (unextractedTokenExperiment_succProbability_le_extracted expand decWit chalToIdx S
    targetFn checkRel hSound A hm hleaf hfs).trans ?_
  exact add_le_add_left (extracted_succProbability_le S targetFn _) _

end AnonymousTokenBridge


/-! ### Bridge to `AnonymousToken.Conservation` -/

section ConservationBridge

/-- Public issuance statement proven by a client in the unextracted ROM conservation game. -/
structure ROMIssueStatement (Context Commitment : Type) where
  /-- Issuer context bound into the issued note commitment. -/
  ctx : Context
  /-- Issued credit amount. -/
  amount : ℕ
  /-- Commitment hiding `(nullifier, opening)` under `ctx` and `amount`. -/
  commitment : Commitment
  deriving DecidableEq

/-- Public spend statement proven by a client in the unextracted ROM conservation game. -/
structure ROMSpendStatement (Nullifier Context Commitment : Type) where
  /-- Issuer context bound into both input note and change commitment. -/
  ctx : Context
  /-- Spent input nullifier revealed publicly to prevent double-spending. -/
  nullifier : Nullifier
  /-- Publicly debited credit amount. -/
  debit : ℕ
  /-- Public refund amount granted by the issuer on the change note. -/
  refund : ℕ
  /-- Commitment to the fresh change note `(newNullifier, ctx, newCredit, newOpening)`. -/
  changeCommitment : Commitment
  deriving DecidableEq

/-- Public issue or spend query sent to the unextracted ROM issuer oracle (without secret note
openings, old note balances, or the input signature). -/
inductive ROMConservationQuery (Nullifier Context Commitment : Type) where
  /-- Request to certify an issuance commitment for `(ctx, amount)`. -/
  | issue (stmt : ROMIssueStatement Context Commitment)
  /-- Request to spend `nullifier` for `debit` and certify `changeCommitment` with `refund`. -/
  | spend (stmt : ROMSpendStatement Nullifier Context Commitment)
  deriving DecidableEq


/-- Signed output message produced when the issuer accepts a public conservation query. -/
@[expose] def ROMConservationQuery.signedMessage {Nullifier Context Commitment Target : Type}
    (tag : Commitment → ℕ → Target) :
    ROMConservationQuery Nullifier Context Commitment → Target
  | .issue q => tag q.commitment 0
  | .spend q => tag q.changeCommitment q.refund

/-- Public VOLEitH statement binding the issuer public key `publicKey` and public `query`. -/
structure ROMConservationStmt (PK Nullifier Context Commitment : Type) where
  /-- Issuer public verification key bound into the Fiat–Shamir query. -/
  publicKey : PK
  /-- Public issuance or spend statement proven in zero knowledge. -/
  query : ROMConservationQuery Nullifier Context Commitment
  deriving DecidableEq

/-- Secret witness extracted from a valid issuance proof. -/
structure ROMIssueWitness (Nullifier Opening : Type) where
  /-- Hidden nullifier committed inside the issued note. -/
  nullifier : Nullifier
  /-- Commitment randomness opening the issued commitment. -/
  opening : Opening
  deriving DecidableEq

/-- Secret witness extracted from a valid spend proof. -/
structure ROMSpendWitness (Nullifier Opening Sig : Type) where
  /-- Hidden credit balance on the spent input note. -/
  oldCredit : ℕ
  /-- Commitment opening for the spent input note. -/
  oldOpening : Opening
  /-- Hidden refund balance on the spent input note. -/
  oldRefund : ℕ
  /-- Issuer signature certifying the spent input note target. -/
  signature : Sig
  /-- Fresh nullifier hidden in the change commitment. -/
  newNullifier : Nullifier
  /-- Remaining credit balance committed in the change note. -/
  newCredit : ℕ
  /-- Commitment randomness for the change note. -/
  newOpening : Opening
  deriving DecidableEq

/-- Extracted conservation witness matching `ROMConservationQuery`. -/
inductive ROMConservationWitness (Nullifier Opening Sig : Type) where
  /-- Witness for an issuance proof. -/
  | issue (wit : ROMIssueWitness Nullifier Opening)
  /-- Witness for a spend proof. -/
  | spend (wit : ROMSpendWitness Nullifier Opening Sig)
  deriving DecidableEq

/-- Client request in the unextracted ROM conservation game, pairing a public query with its
straight-line extractable VOLEitH proof. -/
structure ROMConservationRequest (Nullifier Context Commitment : Type) (d comLen rowLen : ℕ)
    (Seed IV PreMsg : Type) where
  /-- Public issue or spend query visible to the issuer. -/
  query : ROMConservationQuery Nullifier Context Commitment
  /-- VOLEitH proof for `⟨pk, query⟩`. -/
  proof : VOLEITHProof d comLen rowLen Seed IV PreMsg
  deriving DecidableEq

/-- Public VOLEitH relation checked in the ROM credit-conservation game: an issuance proof opens
the issued commitment, and a spend proof proves a valid input signature, change commitment opening,
and note balance conservation `oldCredit + oldRefund = newCredit + debit`. -/
@[expose] def romConservationRel {PK SK Nullifier Context Opening Commitment Target Sig : Type}
    [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (stmt : ROMConservationStmt PK Nullifier Context Commitment) :
    ROMConservationWitness Nullifier Opening Sig → Bool
  | wit =>
    match stmt.query, wit with
    | .issue q, .issue w => decide (com w.nullifier q.ctx q.amount w.opening = q.commitment)
    | .spend q, .spend w =>
      S.verify stmt.publicKey
          (Credit.target com tag ⟨q.nullifier, q.ctx, w.oldCredit, w.oldRefund⟩ w.oldOpening)
          w.signature &&
        decide (com w.newNullifier q.ctx w.newCredit w.newOpening = q.changeCommitment) &&
        decide (w.oldCredit + w.oldRefund = w.newCredit + q.debit)
    | _, _ => false

/-- Assemble a full `Conservation.Request` from a public ROM request and an extracted witness,
preserving all public fields unconditionally. -/
private def romConservationToExtractedRequest
    {Nullifier Context Commitment Opening Sig : Type}
    {d comLen rowLen : ℕ} {Seed IV PreMsg : Type}
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (wit : ROMConservationWitness Nullifier Opening Sig) :
    Conservation.Request Nullifier Context Opening Commitment Sig :=
  match req.query with
  | .issue q =>
    match wit with
    | .issue w => .issue ⟨q.ctx, q.amount, q.commitment, w.nullifier, w.opening⟩
    | .spend _ => .issue ⟨q.ctx, q.amount, q.commitment, default, default⟩
  | .spend q =>
    match wit with
    | .spend w =>
      .spend ⟨q.ctx, q.nullifier, q.debit, q.refund, q.changeCommitment,
        w.oldCredit, w.oldOpening, w.oldRefund, w.signature,
        w.newNullifier, w.newCredit, w.newOpening⟩
    | .issue _ =>
      .spend ⟨q.ctx, q.nullifier, q.debit, q.refund, q.changeCommitment,
        0, default, 0, default, default, 0, default⟩


/-- Project a full `Conservation.Request` onto its public `ROMConservationQuery`. -/
private def romConservationToPublicQuery {Nullifier Context Opening Commitment Sig : Type} :
    Conservation.Request Nullifier Context Opening Commitment Sig →
      ROMConservationQuery Nullifier Context Commitment
  | .issue r => .issue ⟨r.ctx, r.amount, r.commitment⟩
  | .spend r => .spend ⟨r.ctx, r.nullifier, r.debit, r.refund, r.changeCommitment⟩

private theorem romConservationToPublicQuery_toExtractedRequest
    {Nullifier Context Commitment Opening Sig : Type}
    {d comLen rowLen : ℕ} {Seed IV PreMsg : Type}
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (wit : ROMConservationWitness Nullifier Opening Sig) :
    romConservationToPublicQuery (romConservationToExtractedRequest req wit) = req.query := by
  rcases req with ⟨q, proof⟩
  cases q <;> cases wit <;> rfl

private theorem signedMessage_toExtractedRequest
    {Nullifier Context Commitment Opening Target Sig : Type}
    {d comLen rowLen : ℕ} {Seed IV PreMsg : Type}
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (tag : Commitment → ℕ → Target)
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (wit : ROMConservationWitness Nullifier Opening Sig) :
    (romConservationToExtractedRequest req wit).signedMessage tag =
    req.query.signedMessage tag := by
  rcases req with ⟨q, proof⟩
  cases q <;> cases wit <;> rfl

private theorem acceptLocal_toExtractedRequest_of_rel
    {PK SK Nullifier Context Opening Commitment Target Sig : Type}
    {d comLen rowLen : ℕ} {Seed IV PreMsg : Type}
    [DecidableEq Commitment] [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK)
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (wit : ROMConservationWitness Nullifier Opening Sig)
    (hrel : romConservationRel com tag S ⟨pk, req.query⟩ wit = true) :
    Conservation.acceptLocal com tag S pk (romConservationToExtractedRequest req wit) = true := by
  rcases req with ⟨q, _⟩
  cases q <;> cases wit <;>
    simp_all [romConservationRel, romConservationToExtractedRequest, Conservation.acceptLocal,
      Conservation.SpendRequest.inputNote]

/-- Nullifier spend check on public conservation queries. -/
@[expose] def romHasSpentNullifier {Nullifier Context Commitment : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    (qs : List (ROMConservationQuery Nullifier Context Commitment))
    (ctx : Context) (nf : Nullifier) : Bool :=
  qs.any fun
    | .issue _ => false
    | .spend s => decide (s.ctx = ctx ∧ s.nullifier = nf)

/-- Public nullifier-freshness check applied by the ROM issuer after proof verification. -/
@[expose] def romAcceptQuery {Nullifier Context Commitment : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    (accepted : List (ROMConservationQuery Nullifier Context Commitment)) :
    ROMConservationQuery Nullifier Context Commitment → Bool
  | .issue _ => true
  | .spend s => !romHasSpentNullifier accepted s.ctx s.nullifier

/-- Total issued credit in `ctx` over public queries. -/
@[expose] def romIssuedAmount {Nullifier Context Commitment : Type} [DecidableEq Context]
    (qs : List (ROMConservationQuery Nullifier Context Commitment)) (ctx : Context) : ℕ :=
  (qs.filterMap fun
    | .issue q => if q.ctx = ctx then some q.amount else none
    | .spend _ => none).sum

/-- Total granted refunds in `ctx` over public queries. -/
@[expose] def romGrantedRefund {Nullifier Context Commitment : Type} [DecidableEq Context]
    (qs : List (ROMConservationQuery Nullifier Context Commitment)) (ctx : Context) : ℕ :=
  (qs.filterMap fun
    | .issue _ => none
    | .spend q => if q.ctx = ctx then some q.refund else none).sum

/-- Total spent debits in `ctx` over public queries. -/
@[expose] def romSpentDebit {Nullifier Context Commitment : Type} [DecidableEq Context]
    (qs : List (ROMConservationQuery Nullifier Context Commitment)) (ctx : Context) : ℕ :=
  (qs.filterMap fun
    | .issue _ => none
    | .spend q => if q.ctx = ctx then some q.debit else none).sum

private theorem romHasSpentNullifier_map {Nullifier Context Opening Commitment Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    (reqs : List (Conservation.Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) (nf : Nullifier) :
    romHasSpentNullifier (reqs.map romConservationToPublicQuery) ctx nf =
      Conservation.hasSpentNullifier reqs ctx nf := by
  simp only [romHasSpentNullifier, Conservation.hasSpentNullifier, List.any_map]
  exact congrArg _ (funext fun x => by cases x <;> rfl)

private theorem romIssuedAmount_map {Nullifier Context Opening Commitment Sig : Type}
    [DecidableEq Context]
    (reqs : List (Conservation.Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) :
    romIssuedAmount (reqs.map romConservationToPublicQuery) ctx =
      Conservation.issuedAmount reqs ctx := by
  simp only [romIssuedAmount, Conservation.issuedAmount, Conservation.issuesIn,
    List.filterMap_map, List.map_filterMap]
  exact congrArg (fun f => (reqs.filterMap f).sum) (funext fun r => by
    cases r <;> simp [romConservationToPublicQuery, apply_ite])

private theorem romGrantedRefund_map {Nullifier Context Opening Commitment Sig : Type}
    [DecidableEq Context]
    (reqs : List (Conservation.Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) :
    romGrantedRefund (reqs.map romConservationToPublicQuery) ctx =
      Conservation.grantedRefund reqs ctx := by
  simp only [romGrantedRefund, Conservation.grantedRefund, Conservation.spendsIn,
    Conservation.spends, List.filterMap_map, List.filter_filterMap, List.map_filterMap]
  exact congrArg (fun f => (reqs.filterMap f).sum) (funext fun r => by
    cases r <;> simp [romConservationToPublicQuery, Option.filter, apply_ite])

private theorem romSpentDebit_map {Nullifier Context Opening Commitment Sig : Type}
    [DecidableEq Context]
    (reqs : List (Conservation.Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) :
    romSpentDebit (reqs.map romConservationToPublicQuery) ctx =
      Conservation.spentDebit reqs ctx := by
  simp only [romSpentDebit, Conservation.spentDebit, Conservation.spendsIn,
    Conservation.spends, List.filterMap_map, List.filter_filterMap, List.map_filterMap]
  exact congrArg (fun f => (reqs.filterMap f).sum) (funext fun r => by
    cases r <;> simp [romConservationToPublicQuery, Option.filter, apply_ite])

/-- Signing oracle specification returning `some sig` on accepted ROM conservation requests and
`none` otherwise. -/
abbrev ROMConservationIssuerSpec (Nullifier Context Commitment : Type) (d comLen rowLen : ℕ)
    (Seed IV PreMsg Sig : Type) :
    OracleSpec
      (ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg) :=
  fun _ => Option Sig

/-- Combined oracle specification exposed to an unextracted ROM conservation adversary. -/
abbrev ROMConservationSpec (Nullifier Context Commitment : Type) (d sdLen comLen rowLen : ℕ)
    (PK Seed IV PreMsg Chal Sig : Type) :=
  ROMConservationIssuerSpec Nullifier Context Commitment d comLen rowLen Seed IV PreMsg Sig ⊕ₒ
    VOLEITHROSpec d sdLen comLen rowLen
      (ROMConservationStmt PK Nullifier Context Commitment) Seed IV PreMsg Chal

/-- Transcript of an unextracted ROM credit-conservation adversary execution. -/
structure ROMConservationExecution (PK Nullifier Context Commitment : Type) where
  /-- Issuer public verification key. -/
  publicKey : PK
  /-- Target context output by the adversary. -/
  targetCtx : Context
  /-- Public queries accepted by the ROM issuer in order. -/
  acceptedQueries : List (ROMConservationQuery Nullifier Context Commitment)

/-- Winning condition for the unextracted ROM conservation adversary: overspending `run.targetCtx`
against `issuedAmount + grantedRefund`. -/
@[expose] def romConservationAccept {PK Nullifier Context Commitment : Type} [DecidableEq Context]
    (run : ROMConservationExecution PK Nullifier Context Commitment) : Bool :=
  decide (romIssuedAmount run.acceptedQueries run.targetCtx +
    romGrantedRefund run.acceptedQueries run.targetCtx <
      romSpentDebit run.acceptedQueries run.targetCtx)

/-- Acceptance continuation for `ROMConservationSpec` that checks `romAcceptQuery`, signs
`req.query.signedMessage tag`, and logs `req.query`. -/
@[expose] noncomputable def romConsAcceptReal {d comLen rowLen : ℕ}
    {PK SK Nullifier Context Commitment Target Seed IV PreMsg Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    (tag : Commitment → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (accepted : List (ROMConservationQuery Nullifier Context Commitment)) :
    ProbComp (Option Sig × List (ROMConservationQuery Nullifier Context Commitment)) :=
  if romAcceptQuery accepted req.query then
    (S.sign keys.2 (req.query.signedMessage tag)).map fun sig =>
      (some sig, accepted ++ [req.query])
  else
    pure (none, accepted)

/-- Execute an unextracted ROM credit-conservation adversary against the VOLEitH-checked issuer
oracle and lazy two-channel ROM. -/
@[expose] noncomputable def runROMUnextractedConservation {d sdLen comLen rowLen : ℕ}
    {PK SK Nullifier Context Commitment Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (tag : Commitment → ℕ → Target)
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (S : Signature.Scheme PK SK Target Sig)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context) :
    ProbComp (ROMConservationExecution PK Nullifier Context Commitment) := do
  let keys ← S.keyGen
  let ⟨targetCtx, _, acceptedQueries⟩ ← ((A keys.1).runState
    (verifyGatedHandlerProg (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof
      checkRel none (romConsAcceptReal tag S keys))).run (([], []), [])
  pure { publicKey := keys.1, targetCtx := targetCtx, acceptedQueries := acceptedQueries }

/-- Unextracted ROM credit-conservation experiment, original to this library (client `query`
fields are public, while note commitments, openings, old balances, and input signatures are
proven in zero knowledge): wins if the accepted ROM query transcript overspends
`run.targetCtx`. -/
@[expose] noncomputable def romUnextractedConservationExperiment {d sdLen comLen rowLen : ℕ}
    {PK SK Nullifier Context Commitment Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (tag : Commitment → ℕ → Target)
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (S : Signature.Scheme PK SK Target Sig)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context) : Experiment :=
  romConservationAccept <$>
    runROMUnextractedConservation expand chalToIdx tag checkRel S A

private noncomputable def consToExtractedInner {d sdLen comLen rowLen : ℕ}
    {PK Nullifier Context Opening Commitment Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (pk : PK) :
    (q : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg ⊕
      (LeafQuery d Seed IV ⊕
        FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)) →
      StateT (VOLEITHTraceState d sdLen comLen rowLen
          (ROMConservationStmt PK Nullifier Context Commitment) Seed IV PreMsg Chal)
        (ProbOracleComp (fun _ : Conservation.Request Nullifier Context Opening Commitment Sig =>
          Option Sig))
        (ROMConservationSpec Nullifier Context Commitment d sdLen comLen rowLen
          PK Seed IV PreMsg Chal Sig q)
  | .inl req, roSt => do
    let (ok, roSt') ← ProbOracleComp.sample ((ProbOracleComp.runState
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel
        ⟨pk, req.query⟩ req.proof)
      voleithMemoizeProg).run roSt)
    if ok then
      let wit := extractWitnessFromTrace expand decWit roSt.1 req.proof
      let sig ← ProbOracleComp.query (romConservationToExtractedRequest req wit)
      pure (sig, roSt')
    else
      pure (none, roSt')
  | .inr qRO, roSt => do
    let (ans, roSt') ← ProbOracleComp.sample ((voleithMemoizeProg qRO).run roSt)
    pure (ans, roSt')

/-- Straight-line extracted-model `Conservation.ExtractedAdversary` constructed from an
unextracted ROM conservation adversary `A`: simulates `VOLEITHROSpec` locally, checks
`voleithVerifyROM`, and whenever a request verifies, extracts the witness without rewinding and
forwards `romConservationToExtractedRequest req wit` to the extracted issuer oracle. -/
noncomputable def extractedAdversaryOfROM {d sdLen comLen rowLen : ℕ}
    {PK Nullifier Context Opening Commitment Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context) :
    Conservation.ExtractedAdversary Nullifier Context Opening Commitment PK Sig := fun pk =>
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (consToExtractedInner expand decWit chalToIdx checkRel pk))
    (A pk)).run ([], [])

/-- `extractedAdversaryOfROM` preserves issuer-query budgets: every `VOLEITHROSpec` call costs `0`
extracted issuer queries and every ROM request calls the extracted issuer at most once. -/
theorem extractedAdversaryOfROM_isQueryBounded {d sdLen comLen rowLen : ℕ}
    {PK Nullifier Context Opening Commitment Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context)
    {m : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m) :
    ∀ pk, (extractedAdversaryOfROM expand decWit chalToIdx checkRel A pk).IsQueryBounded m := by
  intro pk
  unfold extractedAdversaryOfROM
  rw [ProbOracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
  refine run_interpret_sumUnif_isCostBounded
    (consToExtractedInner expand decWit chalToIdx checkRel pk)
    (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun req roSt => ?_) (fun qRO roSt => ?_)
    (A pk) ([], []) (hm pk)
  · simpa only [StateT.run, consToExtractedInner] using
      isCostBounded_sample_ite_query
        (spec := fun _ : Conservation.Request Nullifier Context Opening Commitment Sig =>
          Option Sig)
        (R := Option Sig)
        ((ProbOracleComp.runState
          (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel ⟨pk, req.query⟩ req.proof)
          voleithMemoizeProg).run roSt)
        (romConservationToExtractedRequest req
          (extractWitnessFromTrace expand decWit roSt.1 req.proof))
        (fun roSt' sig => (sig, roSt')) (fun roSt' => (none, roSt'))
  · simpa only [StateT.run, consToExtractedInner] using
      isCostBounded_sample_bind_pure_zero _ _ _

private noncomputable def romConsAcceptExt {d sdLen comLen rowLen : ℕ}
    {PK SK Nullifier Context Opening Commitment Target Seed IV PreMsg Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq IV] [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (tr₁ : LeafTrace d sdLen comLen Seed IV)
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (accepted : List (ROMConservationQuery Nullifier Context Commitment)) :
    ProbComp (Option Sig × List (ROMConservationQuery Nullifier Context Commitment)) :=
  let extReq := romConservationToExtractedRequest req
    (extractWitnessFromTrace expand decWit tr₁ req.proof)
  if Conservation.acceptLocal com tag S keys.1 extReq && romAcceptQuery accepted req.query then
    (S.sign keys.2 (extReq.signedMessage tag)).map fun sig =>
      (some sig, accepted ++ [req.query])
  else
    pure (none, accepted)

/-- Concrete query-bounded advantage bound (not an asymptotic PPT security theorem):
reduction from the unextracted ROM credit-conservation game to
`Conservation.extractedConservationExperiment`: an adversary making at most `m` signing queries,
`Q_leaf` leaf RO queries, and `Q_FS` Fiat–Shamir queries loses at most
`voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel` when lifted to the extracted
conservation experiment via `extractedAdversaryOfROM`. -/
theorem unextractedConservationExperiment_succProbability_le_extracted {d sdLen comLen rowLen : ℕ}
    {PK SK Nullifier Context Opening Commitment Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen
      (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx (romConservationRel com tag S) checkRel ε_rel)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context)
    {m Q_leaf Q_FS : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m)
    (hleaf : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) (A pk) Q_leaf)
    (hfs : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) (A pk) Q_FS) :
    (romUnextractedConservationExperiment expand chalToIdx tag checkRel S A).succProbability ≤
      (Conservation.extractedConservationExperiment com tag S
        (extractedAdversaryOfROM expand decWit chalToIdx checkRel A)).succProbability +
        voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel := by
  let extH := fun keys : PK × SK =>
    verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof checkRel
      (none : Option Sig) (romConsAcceptExt expand decWit com tag S keys)
  let romH := fun keys : PK × SK =>
    verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof checkRel
      (none : Option Sig) (fun _ => romConsAcceptReal tag S keys)
  have hrom_eval :
      ProbComp.eval (romUnextractedConservationExperiment expand chalToIdx tag checkRel S A) =
        (ProbComp.eval S.keyGen).bind fun keys =>
          (ProbOracleComp.runWith (romH keys) (A keys.1) (([], []), [])).map
            fun (ctx, (_, accepted)) =>
              decide (romIssuedAmount accepted ctx + romGrantedRefund accepted ctx <
                romSpentDebit accepted ctx) := by
    simp only [romUnextractedConservationExperiment, runROMUnextractedConservation,
      ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_runState,
      PMF.map_bind]
    congr 1 with keys : 1
    simp only [romH, verifyGatedHandlerProg_eval, PMF.map, Function.comp_def, PMF.pure_bind,
      romConservationAccept]
  have hext_eval :
      ProbComp.eval (Conservation.extractedConservationExperiment com tag S
        (extractedAdversaryOfROM expand decWit chalToIdx checkRel A)) =
        (ProbComp.eval S.keyGen).bind fun keys =>
          (ProbOracleComp.runWith (extH keys) (A keys.1) (([], []), [])).map
            fun (ctx, (_, accepted)) =>
              decide (romIssuedAmount accepted ctx + romGrantedRefund accepted ctx <
                romSpentDebit accepted ctx) := by
    simp only [Conservation.extractedConservationExperiment,
      Conservation.runExtractedConservation, extractedAdversaryOfROM, ProbComp.eval_map,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.map, PMF.bind_bind, Function.comp_def,
      PMF.pure_bind]
    congr 1 with keys : 1
    let issuerH : Conservation.Request Nullifier Context Opening Commitment Sig →
        StateT (List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig))
          PMF (Option Sig) := fun q log =>
      if Conservation.acceptRequest com tag S keys.1 (log.map Prod.fst) q then
        (ProbComp.eval (S.sign keys.2 (q.signedMessage tag))).map fun sig =>
          (some sig, log ++ [(q, some sig)])
      else
        PMF.pure (none, log)
    let extRun := (OracleComp.interpret
      (OracleComp.sumHandler
        (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (consToExtractedInner expand decWit chalToIdx checkRel keys.1))
      (A keys.1)).run ([], [])
    have hlog_map :
        ProbComp.eval ((Prod.fst <$> extRun).runLogWith
            (Conservation.extractedIssuerOracle com tag S keys)) =
          (ProbOracleComp.runWith issuerH extRun []).map (Prod.map Prod.fst id) := by
      simp only [ProbOracleComp.runLogWith, ProbOracleComp.runState_map, StateT.run_map,
        ProbOracleComp.eval_runState, ProbComp.eval_map]
      congr 2 with q log
      simp only [ProbOracleComp.logOracle, Conservation.extractedIssuerOracle, issuerH]
      cases Conservation.acceptRequest com tag S keys.1 (log.map Prod.fst) q
      · simp only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]
        rfl
      · simp only [↓reduceIte, ProbComp.eval_map, PMF.map_comp, Function.comp_def]
    erw [hlog_map]
    have hrun := ProbOracleComp.runWith_run_interpret
      (consToExtractedInner expand decWit chalToIdx checkRel keys.1) issuerH (A keys.1) ([], []) []
    let repCons : VOLEITHTraceState d sdLen comLen rowLen
          (ROMConservationStmt PK Nullifier Context Commitment) Seed IV PreMsg Chal ×
        List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig) →
        VOLEITHTraceState d sdLen comLen rowLen
          (ROMConservationStmt PK Nullifier Context Commitment) Seed IV PreMsg Chal ×
          List (ROMConservationQuery Nullifier Context Commitment) :=
      fun (roSt, log) => (roSt, log.map (romConservationToPublicQuery ∘ Prod.fst))
    have hjoint_eq :
        ((ProbOracleComp.runWith
            (fun q state =>
              PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
                (ProbOracleComp.runWith issuerH
                  ((consToExtractedInner expand decWit chalToIdx checkRel keys.1 q).run state.1)
                  state.2))
            (A keys.1) (([], []), [])).map (Prod.map id repCons)) =
          ProbOracleComp.runWith (extH keys) (A keys.1) (([], []), []) := by
      refine ProbOracleComp.runWith_map_state _ _ repCons (fun q x => ?_)
        (A keys.1) (([], []), [])
      rcases x with ⟨roSt, log⟩
      rcases q with req | qRO
      · simp only [consToExtractedInner, StateT.run, ProbOracleComp.runWith_bind,
          ProbOracleComp.runWith_sample, extH, verifyGatedHandler,
          eval_runState_voleithMemoizeProg, PMF.map, PMF.bind_bind, Function.comp_def,
          PMF.pure_bind]
        congr 1 with ⟨ok, roSt'⟩ : 1
        cases ok
        · simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure, PMF.pure_bind,
            repCons]
        · simp only [↓reduceIte, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
            ProbOracleComp.runWith_pure, issuerH, repCons, Function.comp_def]
          set extReq := romConservationToExtractedRequest req
            (extractWitnessFromTrace expand decWit roSt.1 req.proof)
          have hacc_eq :
              Conservation.acceptRequest com tag S keys.1 (log.map Prod.fst) extReq =
                (Conservation.acceptLocal com tag S keys.1 extReq &&
                  romAcceptQuery (log.map fun x =>
                    romConservationToPublicQuery x.1) req.query) := by
            rcases req with ⟨q, proof⟩
            cases q with
            | issue iq =>
              simp only [extReq, romConservationToExtractedRequest, Conservation.acceptRequest,
                romAcceptQuery, Bool.and_true]
              cases extractWitnessFromTrace expand decWit roSt.1 proof <;> rfl
            | spend sq =>
              simp only [extReq, romConservationToExtractedRequest]
              cases hwt : extractWitnessFromTrace expand decWit roSt.1 proof <;>
                simp [Conservation.acceptRequest, romAcceptQuery, ← romHasSpentNullifier_map,
                  List.map_map, Function.comp_def]
          rw [hacc_eq]
          cases hacc :
              Conservation.acceptLocal com tag S keys.1 extReq &&
                romAcceptQuery (log.map fun x => romConservationToPublicQuery x.1) req.query
          · simp only [romConsAcceptExt, extReq, hacc, Bool.false_eq_true, ↓reduceIte,
              ProbComp.eval_pure, PMF.pure_bind]
          · simp only [hacc, ↓reduceIte, PMF.map, PMF.bind_bind, Function.comp_def,
              PMF.pure_bind, List.map_append, List.map_cons, List.map_nil, extReq,
              romConservationToPublicQuery_toExtractedRequest, romConsAcceptExt,
              ProbComp.eval_freeMMap]
      · simp only [consToExtractedInner, StateT.run, ProbOracleComp.runWith_bind,
          ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure, repCons, extH,
          verifyGatedHandler, PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind,
          eval_voleithMemoizeProg]
    rw [hrun, ← hjoint_eq]
    simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind,
      Conservation.extractedConservationAccept, repCons, Prod.map, id_eq]
    congr 1 with ⟨ctx, roSt, log⟩ : 1
    rw [← romIssuedAmount_map, ← romGrantedRefund_map, ← romSpentDebit_map, List.map_map]
    rfl
  exact bind_tsum_add_voleithKSBound_toNNReal _ _ (ProbComp.eval S.keyGen) _ _ _
    (fun keys => toOuterMeasure_runWith_verifyGatedHandler_le expand decWit chalToIdx
      (romConservationRel com tag S) (fun req => ⟨keys.1, req.query⟩)
      ROMConservationRequest.proof checkRel hSound none (romConsAcceptReal tag S keys)
      (romConsAcceptExt expand decWit com tag S keys)
      (fun tr req accepted hrel => by
        simp [romConsAcceptReal, romConsAcceptExt,
          acceptLocal_toExtractedRequest_of_rel com tag S keys.1 req _ hrel,
          signedMessage_toExtractedRequest tag req])
      [] (A keys.1) (hm keys.1) (hleaf keys.1) (hfs keys.1)
      (fun (ctx, (_, accepted)) =>
        decide (romIssuedAmount accepted ctx + romGrantedRefund accepted ctx <
          romSpentDebit accepted ctx)))
    hrom_eval hext_eval

/-- Concrete query-bounded advantage bound (not an asymptotic PPT security theorem):
end-to-end ROM reduction for `AnonymousToken.Conservation` composing straight-line leaf
extraction with `Conservation.extractedConservationExperiment_succProbability_le_prod_mk` to bound
an unextracted ROM conservation adversary's overspending probability by EUF-CMA against
`noteForger`, commitment binding against `commitmentBindingReduction`, and `voleithKSBound`. -/
theorem unextractedConservationExperiment_succProbability_le_prod_mk
    {d sdLen comLen rowLen : ℕ}
    {K PK SK Nullifier Context Opening Commitment Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen
      (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (hverify : ∀ k nf ctx t c o, CS.verify k (nf, ctx, t) c o = decide (com nf ctx t o = c))
    (S : Signature.Scheme PK SK (Commitment × ℕ) Sig)
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx (romConservationRel com Prod.mk S)
      checkRel ε_rel)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context)
    {m Q_leaf Q_FS : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m)
    (hleaf : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) (A pk) Q_leaf)
    (hfs : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) (A pk) Q_FS) :
    (romUnextractedConservationExperiment expand chalToIdx Prod.mk checkRel S A).succProbability ≤
      (S.eufCmaExperiment (targetForger (Credit.target com Prod.mk)
          (Conservation.noteForger com Prod.mk S
            (extractedAdversaryOfROM expand decWit chalToIdx checkRel A)))).succProbability +
        (CS.bindingExperiment (Conservation.commitmentBindingReduction com S
          (extractedAdversaryOfROM expand decWit chalToIdx checkRel A))).succProbability +
        voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel := by
  refine (unextractedConservationExperiment_succProbability_le_extracted expand decWit chalToIdx
    com Prod.mk S checkRel hSound A hm hleaf hfs).trans ?_
  exact add_le_add_left
    (Conservation.extractedConservationExperiment_succProbability_le_prod_mk
      com CS hverify S _) _

end ConservationBridge


end Cslib.Crypto.AnonymousToken
