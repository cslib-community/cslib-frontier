/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Crypto.Protocols.AnonymousToken.PolyTime
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for polynomial-time reduction witnesses in `AnonymousToken.PolyTime`

Exercises `Cslib.Crypto.AnonymousToken` and `Cslib.Crypto.AnonymousToken.Conservation` word-level
reductions, polynomial-time / PPT certificates, `PMF` law-equality theorems, and headline
negligibility bounds via a `module` client with ordinary imports:
* encoding injectivity (`encWordPayload.injective`, `wordTag_injective`, `encComInput.injective`)
  and decoder round-trips (`wordPairDecoder`, `wordPayloadDecoder`, `creditNoteDecoder`,
  `wordRequestDecoder`);
* negative boundary check on `Conservation.noteBindingCollisionOrTrivial ... none`;
* concrete `WordSignatureScheme` (`identitySigScheme`), concrete polynomial-time hashes
  (`constHash`, `idHash`), and concrete oracle-PPT adversaries exercising `targetForgerWord`,
  `bindingReductionWord`, `targetCollisionFinder`, `sampledTargetForger`, `noteForgerWord`,
  `commitmentBindingReductionWord`, `sampledConservationForger`, and `noteCollisionFinder`;
* concrete `extractedTokenWordGame` and `extractedConservationWordGame` evaluations (both
  probability-`1` attacks under `constHash` and probability-`0` honest runs), plus concrete
  `idHash`/adversary instantiations of `negligible_extractedTokenWordGame` and
  `negligible_extractedConservationWordGame` assuming only `S.EUFCMA`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.AnonymousTokenPolyTime

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken Cslib.Crypto.AnonymousToken.Conservation
open Cslib.Probability Turing.MultiTapeTM

/-! ### 1. Decoder round-trips and injectivity boundaries -/

example :
    wordPairDecoder.decode (encWordPair ([true, false], [false])) = ([true, false], [false]) :=
  wordPairDecoder.decode_enc _

example :
    wordPayloadDecoder.decode (encWordPayload ⟨[true], [false, true]⟩) = ⟨[true], [false, true]⟩ :=
  wordPayloadDecoder.decode_enc _

example :
    let note : Credit.Note (List Bool) (List Bool) :=
      { nullifier := [true, true], context := [false], credit := 42, refund := 3 }
    creditNoteDecoder.decode (encCreditNote note) = note :=
  creditNoteDecoder.decode_enc _

example :
    let req : Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) :=
      .issue
        { ctx := [true], amount := 17, commitment := [false, true],
          nullifier := [true], opening := [false] }
    wordRequestDecoder.decode (encWordRequest req) = req :=
  wordRequestDecoder.decode_enc _

example :
    let req : Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) :=
      .spend
        { ctx := [true], nullifier := [false], debit := 7, refund := 3,
          changeCommitment := [true, false], oldCredit := 17, oldOpening := [false],
          oldRefund := 0, signature := [true, true], newNullifier := [false, true],
          newCredit := 13, newOpening := [true] }
    wordRequestDecoder.decode (encWordRequest req) = req :=
  wordRequestDecoder.decode_enc _

-- Distinct `(msg, opening)` payloads always map to distinct `encWordPayload` codewords.
example :
    encWordPayload ⟨[true], [false]⟩ ≠ encWordPayload ⟨[false], [true]⟩ := by
  intro h
  have hinj := encWordPayload.injective h
  have : ([true] : List Bool) = [false] := congrArg Payload.message hinj
  cases this

-- Distinct `(commitment, refund)` pairs always map to distinct `wordTag` codewords.
example : wordTag [true] 1 ≠ wordTag [false] 1 := by
  intro h
  have h' : (fun p : List Bool × ℕ => wordTag p.1 p.2) ([true], 1) =
      (fun p : List Bool × ℕ => wordTag p.1 p.2) ([false], 1) := h
  have hinj := wordTag_injective h'
  have : ([true] : List Bool) = [false] := congrArg Prod.fst hinj
  cases this

-- Distinct `(nf, ctx, credit, opening)` records map to distinct `encComInput` words.
example :
    encComInput ⟨[true], [], 5, []⟩ ≠ encComInput ⟨[true], [], 6, []⟩ := by
  intro h
  have hinj := encComInput.injective h
  have : (5 : ℕ) = 6 := congrArg ComInput.credit hinj
  cases this

-- `encComInput` keeps the nested-pair word layout of the former 4-tuple encoding.
example (r : ComInput) :
    encComInput r =
      (encPair encBits (encPair encBits (encPair encNat encBits)))
        (r.nullifier, r.context, r.credit, r.opening) :=
  rfl

-- Negative boundary: `Conservation.noteBindingCollisionOrTrivial ... none` never satisfies
-- `isBindingCollision` for any commitment scheme `CS`.
example {K : Type} (CS : Crypto.Commitment.Scheme K (List Bool × List Bool × ℕ)
      (List Bool) (List Bool))
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (n : ℕ) (ck : List Bool) (key : K) :
    CS.isBindingCollision key
      (Conservation.noteBindingCollisionOrTrivial (com n ck) none) = false := by
  simp [Crypto.Commitment.Scheme.isBindingCollision, Conservation.noteBindingCollisionOrTrivial]

/-! ### 2. Concrete scheme, hash, and word-level PPT adversary fixtures -/

/-- Trivial deterministic word signature scheme signing a message with itself. -/
private def identitySigScheme : WordSignatureScheme where
  keyGen _ := pure ([], [])
  sign _ msg := pure msg
  verify _ msg sig := decide (msg = sig)
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ msg sig hsig
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
    subst hsig
    simp

private def constHash (_ _ : List Bool) : List Bool := []

private theorem computableInPolyTime_constHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => constHash p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold constHash
  polytime

private def idSigBound (_ k : ℕ) : ℕ := k

private theorem computableInPolyTime_idSigBound :
    ComputableInPolyTime (fun p : ℕ × ℕ => idSigBound p.1 p.2) encNatPair encUnary :=
  ComputableInPolyTime.snd encUnary encUnary

private theorem idSigBound_holds (n : ℕ) (pk sk : List Bool)
    (_ : (pk, sk) ∈ (ProbComp.eval (identitySigScheme.keyGen n)).support)
    (msg sig : List Bool) (hsig : sig ∈ (ProbComp.eval (identitySigScheme.sign sk msg)).support) :
    sig.length ≤ idSigBound n msg.length := by
  simp only [identitySigScheme, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
  subst hsig
  exact le_rfl

private theorem computableInPolyTime_constWordPayloadTarget :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool =>
        wordPayloadTarget constHash p.1 p.2.1 p.2.2.1 p.2.2.2)
      encTargetArgs encBits := by
  have h : (fun p : ℕ × List Bool × List Bool × List Bool =>
      wordPayloadTarget constHash p.1 p.2.1 p.2.2.1 p.2.2.2) = fun _ => [] := rfl
  rw [h]
  exact ComputableInPolyTime.const []

private def constNoteCom (_ : ℕ) (_ _ _ : List Bool) (_ : ℕ) (_ : List Bool) : List Bool := []

private theorem computableInPolyTime_constNoteCom :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        constNoteCom p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits := by
  have h : (fun p : (ℕ × List Bool) × ComInput =>
      constNoteCom p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening) =
      fun _ => [] := rfl
  rw [h]
  exact ComputableInPolyTime.const []

private def constPayloadForger (msg : List Bool) : WordExtractedForgerOf (List Bool) :=
  fun _ _ => do
    let sig ← List.take 0 <$> ProbOracleComp.query ((), encWordPayload ⟨[true], []⟩)
    return ⟨⟨msg, []⟩, sig⟩

/-- Concrete word forger that queries `[true]` with opening `[]` and outputs `[false]` with opening
`[]`, triggering a collision under `constHash`. -/
private abbrev collidingWordForger : WordExtractedForgerOf (List Bool) :=
  constPayloadForger [false]

/-- Honest word forger that queries `[true]` and outputs `[true]`. -/
private abbrev honestWordForger : WordExtractedForgerOf (List Bool) :=
  constPayloadForger [true]

private theorem isOraclePPT_constPayloadForger (msg : List Bool) :
    IsOraclePPT encWordToken (constPayloadForger msg) := by
  have hq : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun _ : ℕ × List Bool =>
        List.take 0 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), encWordPayload ⟨[true], []⟩)) :=
    IsOraclePPTOn.query_take () (ComputableInPolyTime.const _) (ComputableInPolyTime.const 0)
  have hret : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        (⟨⟨msg, []⟩, p.2⟩ : Token (List Bool) (List Bool) (List Bool)))
      (encPair (encPair encUnary encBits) encBits) encWordToken :=
    encTokenOf_mk_polyTime encBits
      (ComputableInPolyTime.const (⟨msg, []⟩ : Payload (List Bool) (List Bool)))
      (ComputableInPolyTime.snd _ _)
  simpa only [constPayloadForger, bind_pure_comp] using (hq.map_with hret).isOraclePPT

/-- Concrete note adversary issuing one note under `constNoteCom` and returning context `[true]`. -/
private def sampleNoteReq : IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) :=
  { ctx := [true], amount := 1, commitment := [], nullifier := [false], opening := [] }

private def simpleNoteAdversary : WordExtractedAdversary := fun _ _ => do
  let _ ← List.take 0 <$>
    ProbOracleComp.query ((), encWordRequest (.issue sampleNoteReq))
  return [true]

private theorem isOraclePPT_simpleNoteAdversary : IsOraclePPT encBits simpleNoteAdversary := by
  have hq : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun _ : ℕ × List Bool =>
        List.take 0 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), encWordRequest (.issue sampleNoteReq))) :=
    IsOraclePPTOn.query_take () (ComputableInPolyTime.const _) (ComputableInPolyTime.const 0)
  have hret : ComputableInPolyTime (fun _ : List Bool => ([true] : List Bool)) encBits encBits :=
    ComputableInPolyTime.const _
  simpa only [simpleNoteAdversary, bind_pure_comp] using (hq.map hret).isOraclePPT

private def sampleIssueReplyLen : ℕ :=
  (encOption encBits (some (wordTag [] 0))).length

private def collidingSpendReq (sig : List Bool) :
    SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) :=
  { ctx := [true], nullifier := [false], debit := 10, refund := 0,
    changeCommitment := [], oldCredit := 10, oldOpening := [],
    oldRefund := 0, signature := sig, newNullifier := [true],
    newCredit := 0, newOpening := [] }

/-- Concrete note adversary issuing `1` unit (`sampleNoteReq`) and then spending `10` units using
the returned signature via the commitment collision under `constHash`. -/
private def collidingSpendAdversary : WordExtractedAdversary := fun _ _ => do
  let reply ← List.take sampleIssueReplyLen <$>
    ProbOracleComp.query ((), encWordRequest (.issue sampleNoteReq))
  let sig := ((Decoder.option Decoder.bits).decode reply).getD []
  let _ ← List.take 0 <$>
    ProbOracleComp.query ((), encWordRequest (.spend (collidingSpendReq sig)))
  return [true]

private theorem isOraclePPT_collidingSpendAdversary :
    IsOraclePPT encBits collidingSpendAdversary := by
  have hq1 : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun _ : ℕ × List Bool =>
        List.take sampleIssueReplyLen <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), encWordRequest (.issue sampleNoteReq))) :=
    IsOraclePPTOn.query_take () (ComputableInPolyTime.const _) (ComputableInPolyTime.const _)
  have hdec : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => (Decoder.option Decoder.bits).decode p.2)
      (encPair (encPair encUnary encBits) encBits) (encOption encBits) :=
    (Decoder.option Decoder.bits).computableInPolyTime.comp (ComputableInPolyTime.snd _ _)
  have hsig : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => ((Decoder.option Decoder.bits).decode p.2).getD [])
      (encPair (encPair encUnary encBits) encBits) encBits :=
    ComputableInPolyTime.optionGetDWithInput hdec (ComputableInPolyTime.const [])
  have hspend : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        collidingSpendReq (((Decoder.option Decoder.bits).decode p.2).getD []))
      (encPair (encPair encUnary encBits) encBits) encSpendRequest := by
    unfold collidingSpendReq
    fun_prop
  have hreq2 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        encWordRequest (.spend
          (collidingSpendReq (((Decoder.option Decoder.bits).decode p.2).getD []))))
      (encPair (encPair encUnary encBits) encBits) encBits :=
    (ComputableInPolyTime.of_eq (f := encRequestSum) (encOut := encBits) fun _ => rfl).comp
      ((ComputableInPolyTime.sumInr encIssueRequest encSpendRequest).comp hspend)
  have hq2 : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun p : (ℕ × List Bool) × List Bool =>
        List.take 0 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), encWordRequest (.spend
            (collidingSpendReq (((Decoder.option Decoder.bits).decode p.2).getD []))))) :=
    IsOraclePPTOn.query_take () hreq2 (ComputableInPolyTime.const 0)
  have hret : ComputableInPolyTime (fun _ : List Bool => ([true] : List Bool)) encBits encBits :=
    ComputableInPolyTime.const _
  simpa only [collidingSpendAdversary, bind_pure_comp, bind_assoc] using
    (hq1.bind_with (hq2.map hret)).isOraclePPT

private def idHash (_ m : List Bool) : List Bool := m

private theorem computableInPolyTime_idHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => idHash p.1 p.2)
      (encPair encBits encBits) encBits :=
  ComputableInPolyTime.snd _ _

private theorem collisionResistant_idHash : CollisionResistant idHash := by
  refine CollisionResistantOn.of_negligible fun adv _ => ?_
  have hfalse : ∀ n k m₁ m₂, isCollision idHash (fun _ _ => true) n k m₁ m₂ = false := by
    intro n k m₁ m₂
    by_contra h
    rw [Bool.not_eq_false, isCollision_eq_true_iff] at h
    exact h.2.2.1 h.2.2.2
  have hzero : (fun n => Game.succProbability
      (ProbComp.eval (collisionGame idHash (fun _ _ => true) adv n))) = fun _ => 0 := by
    funext n
    simp only [Game.succProbability, collisionGame, hfalse, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [Cslib.Probability.PMF.bind_apply_of_forall _ fun _ =>
      Cslib.Probability.PMF.bind_apply_of_forall _ fun _ => rfl]
    simp
  simpa only [hzero] using negligible_zero

/-! ### 3. Concrete reduction witnesses, `eval` equalities, and collision witness -/

example :
    IsOraclePPTOn encPublicInput encWordPair
      (fun p => targetForgerWord idSigBound (wordPayloadTarget constHash)
        collidingWordForger p.1 p.2) :=
  isOraclePPTOn_targetForgerWord computableInPolyTime_idSigBound
    computableInPolyTime_constWordPayloadTarget (isOraclePPT_constPayloadForger [false])

example :
    IsOraclePPT (encPair encBits encBits)
      (sampledTargetForger idSigBound constHash collidingWordForger) :=
  isOraclePPT_sampledTargetForger computableInPolyTime_idSigBound computableInPolyTime_constHash
    (isOraclePPT_constPayloadForger [false])

example :
    IsPPTOn encParamInput encOptionWordBindingWitness
      (fun p => bindingReductionWord identitySigScheme (wordPayloadTarget constHash)
        Decoder.bits collidingWordForger p.1 p.2) :=
  isPPTOn_bindingReductionWord identitySigScheme computableInPolyTime_constWordPayloadTarget
    Decoder.bits (isOraclePPT_constPayloadForger [false])

example :
    IsPPT (encPair encBits encBits)
      (targetCollisionFinder identitySigScheme constHash collidingWordForger) :=
  isPPT_targetCollisionFinder identitySigScheme computableInPolyTime_constHash
    (isOraclePPT_constPayloadForger [false])

example (n : ℕ) (ck : List Bool) :
    ProbComp.eval (identitySigScheme.eufCmaGame
      (fun m spk => targetForgerWord idSigBound (wordPayloadTarget constHash)
        collidingWordForger m (spk, ck)) n) =
      ProbComp.eval ((identitySigScheme.toScheme n).eufCmaExperiment
        (targetForger (wordPayloadTarget constHash n ck)
          (WordExtractedForgerOf.toTyped Decoder.bits (collidingWordForger.atKey ck) n))) :=
  eval_eufCmaGame_targetForgerWord_eq identitySigScheme (wordPayloadTarget constHash) idSigBound
    idSigBound_holds collidingWordForger n ck

example (n : ℕ) (ck : List Bool) :
    ProbComp.eval (bindingReductionWord identitySigScheme (wordPayloadTarget constHash)
      Decoder.bits collidingWordForger n ck) =
      ProbComp.eval (bindingReduction (identitySigScheme.toScheme n)
        (wordPayloadTarget constHash n ck)
        (WordExtractedForgerOf.toTyped Decoder.bits (collidingWordForger.atKey ck) n)) :=
  eval_bindingReductionWord_eq identitySigScheme (wordPayloadTarget constHash) Decoder.bits
    collidingWordForger n ck

-- Concrete collision-winning witness: `collidingWordForger` breaks `constHash` via
-- `targetCollisionFinder` with probability `1`.
example (n : ℕ) (ck : List Bool) :
    (ProbComp.eval (do
      let pair ← targetCollisionFinder identitySigScheme constHash collidingWordForger n ck
      return isCollision constHash (fun _ _ => true) n ck pair.1 pair.2)) true = 1 := by
  have hrun :
      ProbComp.eval (targetCollisionFinder identitySigScheme constHash collidingWordForger n ck) =
        PMF.pure (encWordPayload ⟨[false], []⟩, encWordPayload ⟨[true], []⟩) := by
    have hdec : (payloadDecoderOf Decoder.bits).decode (encWordPayload ⟨[true], []⟩) =
        ⟨[true], []⟩ := wordPayloadDecoder.decode_enc _
    simp only [targetCollisionFinder, eval_bindingReductionWord_eq, bindingReduction, runExtracted,
      WordExtractedForgerOf.toTyped, WordExtractedForgerOf.atKey, collidingWordForger,
      constPayloadForger, identitySigScheme, WordSignatureScheme.toScheme, ProbComp.eval_map,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, ProbOracleComp.runLog,
      bind_pure_comp, ProbOracleComp.simulate_map, ProbOracleComp.simulate_query,
      ProbOracleComp.runState_map, ProbOracleComp.runState_query, findBindingWitness,
      wordPayloadTarget, constHash]
    rw [hdec, StateT.run_map, StateT.run_map]
    simp only [StateT.run, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map]
    rfl
  simp [hrun, isCollision, constHash]

example :
    IsOraclePPTOn encParamInput encNoteToken
      (fun p => noteForgerWord idSigBound constNoteCom wordTag identitySigScheme
        simpleNoteAdversary p.1 p.2) :=
  isOraclePPTOn_noteForgerWord computableInPolyTime_idSigBound computableInPolyTime_constNoteCom
    computableInPolyTime_wordTag identitySigScheme isOraclePPT_simpleNoteAdversary

example :
    IsPPTOn encParamInput encWordBindingCollision
      (fun p => commitmentBindingReductionWord idSigBound constNoteCom wordTag
        identitySigScheme simpleNoteAdversary p.1 p.2) :=
  isPPTOn_commitmentBindingReductionWord computableInPolyTime_idSigBound
    computableInPolyTime_constNoteCom computableInPolyTime_wordTag identitySigScheme
    isOraclePPT_simpleNoteAdversary

example :
    IsOraclePPT (encPair encBits encBits)
      (sampledConservationForger idSigBound constHash identitySigScheme simpleNoteAdversary) :=
  isOraclePPT_sampledConservationForger computableInPolyTime_idSigBound
    computableInPolyTime_constHash identitySigScheme isOraclePPT_simpleNoteAdversary

example :
    IsPPT (encPair encBits encBits)
      (noteCollisionFinder idSigBound identitySigScheme constHash simpleNoteAdversary) :=
  isPPT_noteCollisionFinder computableInPolyTime_idSigBound identitySigScheme
    computableInPolyTime_constHash isOraclePPT_simpleNoteAdversary

example (n : ℕ) (ck : List Bool) :
    ProbComp.eval (runExtractedWord identitySigScheme (noteTarget constNoteCom wordTag)
      creditNoteDecoder
      (noteForgerWord idSigBound constNoteCom wordTag identitySigScheme simpleNoteAdversary)
      n ck) =
      ProbComp.eval (runExtracted (pairScheme identitySigScheme wordTag n)
        (Credit.target (constNoteCom n ck) Prod.mk)
        (noteForger (constNoteCom n ck) Prod.mk (pairScheme identitySigScheme wordTag n)
          (simpleNoteAdversary.toTyped n ck))) :=
  eval_runExtracted_noteForgerWord_eq identitySigScheme idSigBound idSigBound_holds constNoteCom
    wordTag simpleNoteAdversary n ck

example (n : ℕ) (ck : List Bool) :
    ProbComp.eval (identitySigScheme.eufCmaGame
      (fun m spk => targetForgerWordOf creditNoteDecoder idSigBound
        (noteTarget constNoteCom wordTag)
        (noteForgerWord idSigBound constNoteCom wordTag identitySigScheme simpleNoteAdversary)
        m (spk, ck)) n) =
      ProbComp.eval ((pairScheme identitySigScheme wordTag n).eufCmaExperiment
        (targetForger (Credit.target (constNoteCom n ck) Prod.mk)
          (noteForger (constNoteCom n ck) Prod.mk (pairScheme identitySigScheme wordTag n)
            (simpleNoteAdversary.toTyped n ck)))) :=
  eval_eufCmaGame_noteForgerWord_eq identitySigScheme idSigBound idSigBound_holds constNoteCom
    wordTag wordTag_injective simpleNoteAdversary n ck

example (n : ℕ) (ck : List Bool) :
    ProbComp.eval (commitmentBindingReductionWord idSigBound constNoteCom wordTag
      identitySigScheme simpleNoteAdversary n ck) =
      ProbComp.eval (Conservation.commitmentBindingReduction (constNoteCom n ck)
        (pairScheme identitySigScheme wordTag n) (simpleNoteAdversary.toTyped n ck) ()) :=
  eval_commitmentBindingReductionWord_eq identitySigScheme idSigBound idSigBound_holds
    constNoteCom wordTag wordTag_injective simpleNoteAdversary n ck ()

/-! ### 4. Concrete word-game evaluations and headline instantiations -/

-- Under `constHash`, `collidingWordForger` wins `extractedTokenWordGame` with probability `1`.
example (n : ℕ) :
    ProbComp.eval (extractedTokenWordGame identitySigScheme constHash collidingWordForger n) true =
      1 := by
  rw [eval_extractedTokenWordGame_eq]
  refine Cslib.Probability.PMF.bind_apply_of_forall _ fun ck => ?_
  have hdec : (payloadDecoderOf Decoder.bits).decode (encWordPayload ⟨[true], []⟩) =
      ⟨[true], []⟩ := wordPayloadDecoder.decode_enc _
  simp only [extractedExperiment, runExtracted, WordExtractedForgerOf.toTyped,
    WordExtractedForgerOf.atKey, collidingWordForger, constPayloadForger, identitySigScheme,
    WordSignatureScheme.toScheme, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.pure_bind, ProbOracleComp.runLog, bind_pure_comp, ProbOracleComp.simulate_map,
    ProbOracleComp.simulate_query, ProbOracleComp.runState_map, ProbOracleComp.runState_query,
    wordPayloadTarget, constHash]
  rw [hdec, StateT.run_map, StateT.run_map]
  simp [StateT.run, extractedAccept, Token.valid, wordPayloadTarget, constHash]

-- An honest forger outputting its queried message `[true]` never wins `extractedTokenWordGame`.
example (n : ℕ) :
    ProbComp.eval (extractedTokenWordGame identitySigScheme constHash honestWordForger n) true =
      0 := by
  rw [eval_extractedTokenWordGame_eq]
  refine Cslib.Probability.PMF.bind_apply_of_forall _ fun ck => ?_
  have hdec : (payloadDecoderOf Decoder.bits).decode (encWordPayload ⟨[true], []⟩) =
      ⟨[true], []⟩ := wordPayloadDecoder.decode_enc _
  simp only [extractedExperiment, runExtracted, WordExtractedForgerOf.toTyped,
    WordExtractedForgerOf.atKey, honestWordForger, constPayloadForger, identitySigScheme,
    WordSignatureScheme.toScheme, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.pure_bind, ProbOracleComp.runLog, bind_pure_comp, ProbOracleComp.simulate_map,
    ProbOracleComp.simulate_query, ProbOracleComp.runState_map, ProbOracleComp.runState_query,
    wordPayloadTarget, constHash]
  rw [hdec, StateT.run_map, StateT.run_map]
  simp [StateT.run, extractedAccept, Token.valid]

-- Under `constHash`, `collidingSpendAdversary` overspends `10 > 1` from a single `1`-unit note
-- and wins `extractedConservationWordGame` with probability `1`.
example (n : ℕ) :
    ProbComp.eval
      (extractedConservationWordGame identitySigScheme constHash collidingSpendAdversary n) true =
      1 := by
  simp only [extractedConservationWordGame, ProbComp.eval_bind]
  refine Cslib.Probability.PMF.bind_apply_of_forall _ fun ck => ?_
  have hdec : ∀ r, wordRequestDecoder.decode (encRequestSum (requestEquiv r)) = r :=
    fun r => wordRequestDecoder.decode_enc r
  have hdecOpt :
      (Decoder.option Decoder.bits).decode (List.take sampleIssueReplyLen
        (true :: wordTag [] 0)) = some (wordTag [] 0) := by
    unfold sampleIssueReplyLen
    rw [show true :: wordTag [] 0 = encOption encBits (some (wordTag [] 0)) from rfl,
      List.take_of_length_le le_rfl, (Decoder.option Decoder.bits).decode_enc]
  simp [extractedConservationExperiment, runExtractedConservation, WordExtractedAdversary.toTyped,
    collidingSpendAdversary, identitySigScheme, pairScheme, wordNoteCom, constHash,
    ProbOracleComp.runLogWith, extractedIssuerOracle, hdec, acceptRequest, acceptLocal,
    Request.signedMessage, sampleNoteReq, hdecOpt, Credit.target, SpendRequest.inputNote,
    hasSpentNullifier, collidingSpendReq, extractedConservationAccept, issuedAmount, issuesIn,
    grantedRefund, spentDebit, spendsIn, spends]

-- Issuing a single note without spends never violates conservation (`0` win probability).
example (n : ℕ) :
    ProbComp.eval
      (extractedConservationWordGame identitySigScheme constHash simpleNoteAdversary n) true =
      0 := by
  simp only [extractedConservationWordGame, ProbComp.eval_bind]
  refine Cslib.Probability.PMF.bind_apply_of_forall _ fun ck => ?_
  have hdec : ∀ r, wordRequestDecoder.decode (encRequestSum (requestEquiv r)) = r :=
    fun r => wordRequestDecoder.decode_enc r
  simp [extractedConservationExperiment, runExtractedConservation, WordExtractedAdversary.toTyped,
    simpleNoteAdversary, identitySigScheme, pairScheme, wordNoteCom, constHash,
    ProbOracleComp.runLogWith, extractedIssuerOracle, hdec, acceptRequest, acceptLocal,
    Request.signedMessage, sampleNoteReq, extractedConservationAccept, issuedAmount, issuesIn,
    grantedRefund, spentDebit, spendsIn, spends]

-- Concrete client instantiations of both asymptotic headlines using `idHash` (unconditionally
-- poly-time and collision-resistant) and concrete PPT adversaries (`collidingWordForger` and
-- `collidingSpendAdversary`), requiring only `S.EUFCMA`.
example (S : WordSignatureScheme) (hS : S.EUFCMA) :
    Negligible (fun n => Game.succProbability
      (ProbComp.eval (extractedTokenWordGame S idHash collidingWordForger n))) :=
  negligible_extractedTokenWordGame S hS idHash computableInPolyTime_idHash
    collisionResistant_idHash collidingWordForger (isOraclePPT_constPayloadForger [false])

example (S : WordSignatureScheme) (hS : S.EUFCMA) :
    Negligible (fun n =>
      Game.succProbability
        (ProbComp.eval (extractedConservationWordGame S idHash collidingSpendAdversary n))) :=
  negligible_extractedConservationWordGame S hS idHash computableInPolyTime_idHash
    collisionResistant_idHash collidingSpendAdversary isOraclePPT_collidingSpendAdversary

end CslibFrontierTests.Crypto.AnonymousTokenPolyTime
