/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Composition
public import CslibFrontier.Crypto.Protocols.UC.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Languages.Probabilistic.Oracle.Support

/-!
# Strict-PPT closure for UC routing and lifting wrappers

This module proves that strict-PPT certificates (`PPTCertificate`, `Machine.IsPPTFamily`,
`Protocol.IsPPT`, `Adversary.IsPPT`) in this library's word model survive the query-adapting,
static-corruption routing, and adversary-lifting wrappers of `UC.Linking`, `UC.Execution`, and
`UC.Composition`. Every construction and theorem here is library infrastructure for this word
model (not Definition 6 of [Canetti2020]).

## Modelling notes

* **Explicit inner cap in `WordInterface.isOraclePPTOn_lowerWith_adapt`.** Translating a lowered
  `J`-oracle program into a lowered `K`-oracle program via a `WordInterface.PortMap` may change
  reply word lengths (for instance, prepending a sum tag bit). The theorem takes an explicit inner
  reply bound `capIn` and a fit hypothesis `hfit` ensuring every translated `r a`-truncated reply
  fits in `capIn a` bits; the polynomial-time reply allowance required by
  `IsOraclePPTOn.interpret_preprocess_open'` is derived directly from `PortMap.replyMap_poly` and
  `hr`, so `capIn` itself needs no computability certificate.
* **Party-index extraction in `routeCorrupt` / `corruptRouter`.** For an arbitrary
  `party : WordPort (Fin n × In) (Option Out)`, `party.queryDecoder` certifies only the re-encoded
  pair `party.query ∘ party.queryDecoder.decode`, which does not in general expose the party index
  `Fin n` in polynomial time. Accordingly, `PPTCertificate.routeCorrupt`,
  `Machine.IsPPTFamily.routeCorrupt`, and `Protocol.IsPPT.corruptRouter` take the minimal hypothesis
  `ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1) encBits (encFinite (Fin n))`,
  which `WordPort.computable_partyIndex` discharges automatically whenever
  `party = WordPort.party input`.
* **State renormalization.** Unforwarded branches of `routeCorrupt` and the pass-through left
  branch of `Machine.liftRight` leave the underlying typed state unchanged, so on arbitrary
  (possibly off-image) state words they invoke `PPTCertificate.normalize`; the pass-through branch
  of `Machine.liftRight` likewise uses `WordInterface.computable_requestNormalize` and
  `WordInterface.computable_replyNormalize`.

## Main definitions

* `Cslib.Crypto.Protocols.UC.WordInterface.PortMap`: polynomial-time word-level translation between
  two `WordInterface`s.
* `Cslib.Crypto.Protocols.UC.WordInterface.PortMap.adapt`: typed `ProbOracleComp.simulate` adapter
  induced by a `PortMap`.
* `Cslib.Crypto.Protocols.UC.WordInterface.PortMap.inr`: right-injection `PortMap` from `iR` into
  `iL.sum iR`.
* `Cslib.Crypto.Protocols.UC.PPTCertificate.routeCorrupt`, `.liftRight`,
  `.liftAdversary`: constructive `PPTCertificate` combinators for corruption routing and lifting.

## Main results

* `Cslib.Crypto.Protocols.UC.WordInterface.isOraclePPTOn_lowerWith_adapt`: adapting a lowered
  strict oracle-PPT program through a `PortMap` preserves `IsOraclePPTOn`.
* `Cslib.Crypto.Protocols.UC.Machine.IsPPTFamily.routeCorrupt`,
  `Cslib.Crypto.Protocols.UC.Protocol.IsPPT.corruptRouter`: static-corruption routing preserves
  strict PPT.
* `Cslib.Crypto.Protocols.UC.Machine.IsPPTFamily.liftRight`,
  `Cslib.Crypto.Protocols.UC.Adversary.IsPPT.liftAdversary`: lifting a machine family or adversary
  past an arbitrary left word interface preserves strict PPT.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 3.2 (Polynomial Time ITMs
  and Parameterized Systems) and Section 4.1 (The Model of Protocol Execution): context for UC
  polynomial time, static-corruption routing, and adversary placement. All results here are
  library constructions for this word model rather than Definition 6 of [Canetti2020].
-/

public section

namespace Cslib.Crypto.Protocols.UC

open Probability Turing.MultiTapeTM

/-! ### Word-level port maps and lowered-program adaptation -/

/-- Library construction (no cited definition): a polynomial-time translation between two
word-backed oracle interfaces, expressing a query-translating `ProbOracleComp.simulate` adapter on
the underlying word interface. -/
structure WordInterface.PortMap {ιJ ιK : Type} {J : ιJ → Type} {K : ιK → Type}
    (iJ : WordInterface J) (iK : WordInterface K) : Type where
  /-- Translate a `J`-query into a `K`-query. -/
  queryMap : ιJ → ιK
  /-- Translate a `K`-reply back into a `J`-reply. -/
  replyBack : (j : ιJ) → K (queryMap j) → J j
  /-- Channel translation on the word interface. -/
  channelMap : iJ.Channel → iK.Channel
  /-- Word-level query translation. -/
  wordMap : iJ.Channel → List Bool → List Bool
  /-- Word-level reply translation. -/
  replyMap : iJ.Channel → List Bool → List Bool
  /-- Compatibility of `channelMap` with `queryMap`. -/
  channelMap_channel : ∀ j, channelMap (iJ.channel j) = iK.channel (queryMap j)
  /-- Compatibility of `wordMap` with `queryMap`. -/
  wordMap_request : ∀ j, wordMap (iJ.channel j) (iJ.request j) = iK.request (queryMap j)
  /-- Compatibility of `replyMap` with `replyBack` on decoded words. -/
  decodeReply_replyMap : ∀ j w,
    iJ.decodeReply j (replyMap (iJ.channel j) w) = replyBack j (iK.decodeReply (queryMap j) w)
  /-- `wordMap` is computable in polynomial time. -/
  wordMap_poly : ComputableInPolyTime (fun x : iJ.Channel × List Bool => wordMap x.1 x.2)
    (encPair (encFinite iJ.Channel) encBits) encBits
  /-- `replyMap` is computable in polynomial time. -/
  replyMap_poly : ComputableInPolyTime (fun x : iJ.Channel × List Bool => replyMap x.1 x.2)
    (encPair (encFinite iJ.Channel) encBits) encBits

/-- Library construction (no cited definition): adapt a `J`-oracle program into a `K`-oracle
program by translating each query with `queryMap` and each reply with `replyBack`. -/
@[expose] def WordInterface.PortMap.adapt {ιJ ιK α : Type} {J : ιJ → Type} {K : ιK → Type}
    {iJ : WordInterface J} {iK : WordInterface K} (m : WordInterface.PortMap iJ iK)
    (program : ProbOracleComp J α) : ProbOracleComp K α :=
  ProbOracleComp.simulate (fun j => m.replyBack j <$> ProbOracleComp.query (m.queryMap j)) program

/-- Library construction (no cited definition): the right-injection `PortMap` embedding `iR` into
`iL.sum iR`. Its `adapt` equals `Machine.liftRightProgram L`. -/
@[expose] def WordInterface.PortMap.inr {ιL ιR : Type} {L : ιL → Type} {R : ιR → Type}
    (iL : WordInterface L) (iR : WordInterface R) :
    WordInterface.PortMap iR (iL.sum iR) where
  queryMap := Sum.inr
  replyBack _ r := r
  channelMap := Sum.inr
  wordMap _ w := w
  replyMap _ w := w
  channelMap_channel _ := rfl
  wordMap_request _ := rfl
  decodeReply_replyMap _ _ := rfl
  wordMap_poly := ComputableInPolyTime.snd (encFinite iR.Channel) encBits
  replyMap_poly := ComputableInPolyTime.snd (encFinite iR.Channel) encBits

private theorem adapt_portMap_inr {ιL ιR α : Type} {L : ιL → Type} {R : ιR → Type}
    (iL : WordInterface L) (iR : WordInterface R) (program : ProbOracleComp R α) :
    (WordInterface.PortMap.inr iL iR).adapt program = Machine.liftRightProgram L program := by
  rw [WordInterface.PortMap.adapt, ProbOracleComp.simulate, Machine.liftRightProgram,
    OracleComp.substitute_eq_interpret]
  apply congrArg (fun h => OracleComp.interpret h program)
  funext q
  cases q with
  | inl k => rfl
  | inr r =>
    simp only [OracleComp.sumHandler, WordInterface.PortMap.inr]
    exact id_map _

/-- Library infrastructure (no cited result): adapting a lowered strict oracle-PPT program through
a `WordInterface.PortMap` preserves `IsOraclePPTOn`, provided every translated `r a`-truncated
reply fits inside the inner reply cap `capIn a`. -/
theorem WordInterface.isOraclePPTOn_lowerWith_adapt {ιJ ιK α β : Type}
    {J : ιJ → Type} {K : ιK → Type}
    {iJ : WordInterface J} {iK : WordInterface K} (m : WordInterface.PortMap iJ iK)
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → ProbOracleComp J β} {r capIn : α → ℕ}
    (hprogram : IsOraclePPTOn input output
      (fun a => ProbOracleComp.lowerWith iJ (capIn a) (program a)))
    (hr : ComputableInPolyTime r input encUnary)
    (hfit : ∀ a c w, (m.replyMap c (List.take (r a) w)).length ≤ capIn a) :
    IsOraclePPTOn input output
      (fun a => ProbOracleComp.lowerWith iK (r a) (m.adapt (program a))) := by
  let handler (a : α) (req : iJ.Channel × List Bool) : WordOracleComp iK.Channel (List Bool) :=
    m.replyMap req.1 <$> (List.take (r a) <$>
      ProbOracleComp.query (spec := fun _ : iK.Channel × List Bool => List Bool)
        (m.channelMap req.1, m.wordMap req.1 req.2))
  have hhandler : IsOraclePPTOn
      (encPair input (encPair (encFinite iJ.Channel) encBits)) encBits
      (fun pair => handler pair.1 pair.2) := by
    let EIn := encPair input (encPair (encFinite iJ.Channel) encBits)
    have htag : ComputableInPolyTime
        (fun pair : α × (iJ.Channel × List Bool) => m.channelMap pair.2.1)
        EIn (encFinite iK.Channel) :=
      (ComputableInPolyTime.of_finite m.channelMap).comp (by dsimp only [EIn]; fun_prop)
    have hword : ComputableInPolyTime
        (fun pair : α × (iJ.Channel × List Bool) => m.wordMap pair.2.1 pair.2.2)
        EIn encBits :=
      m.wordMap_poly.comp (ComputableInPolyTime.snd input (encPair (encFinite iJ.Channel) encBits))
    have hr' : ComputableInPolyTime
        (fun pair : α × (iJ.Channel × List Bool) => r pair.1) EIn encUnary :=
      hr.comp (ComputableInPolyTime.fst input (encPair (encFinite iJ.Channel) encBits))
    have hquery : IsOraclePPTOn EIn encBits
        (fun pair => List.take (r pair.1) <$>
          ProbOracleComp.query (spec := fun _ : iK.Channel × List Bool => List Bool)
            (m.channelMap pair.2.1, m.wordMap pair.2.1 pair.2.2)) :=
      IsOraclePPTOn.query_take_with htag hword hr'
    refine hquery.map_with (f := fun pair reply => m.replyMap pair.2.1 reply) ?_
    have hproj : ComputableInPolyTime
        (fun x : (α × (iJ.Channel × List Bool)) × List Bool => (x.1.2.1, x.2))
        (encPair EIn encBits) (encPair (encFinite iJ.Channel) encBits) := by
      dsimp only [EIn]
      fun_prop
    exact m.replyMap_poly.comp hproj
  obtain ⟨c, d, hreplyBound⟩ := m.replyMap_poly.polyBounded_length.exists_le
  let resources (a : α) (_ : List Bool) : ℕ := c * (2 * Nat.card iJ.Channel + 2 + r a) ^ d
  have hresources : ComputableInPolyTime (fun pair : α × List Bool => resources pair.1 pair.2)
      (encPair input encBits) encUnary := by
    have hpoly : ComputableInPolyTime (fun n : ℕ => c * (2 * Nat.card iJ.Channel + 2 + n) ^ d)
        encUnary encUnary := by
      fun_prop
    exact hpoly.comp (hr.comp (ComputableInPolyTime.fst input encBits))
  have hbound : ∀ (a : α) (req : iJ.Channel × List Bool) (reply : List Bool),
      reply ∈ OracleComp.support (handler a req) → reply.length ≤ resources a req.2 := by
    intro a req reply hmem
    simp only [handler, OracleComp.mem_supportWith_map_iff, ProbOracleComp.supportWith_query,
      Set.mem_univ, true_and] at hmem
    rcases hmem with ⟨u, ⟨w, rfl⟩, rfl⟩
    have hle := hreplyBound (req.1, List.take (r a) w)
    simp only [length_encPair, encBits_apply] at hle
    have hch : (encFinite iJ.Channel req.1).length ≤ Nat.card iJ.Channel :=
      (length_encFinite_lt req.1).le
    have htake : (List.take (r a) w).length ≤ r a := List.length_take_le (r a) w
    refine hle.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left ?_ d))
    omega
  have hsub := hprogram.interpret_preprocess_open'
    (operationEncoding := encFinite iJ.Channel)
    (handler := handler) (prepare := id) (resources := resources)
    ComputableInPolyTime.id' hhandler hresources hbound
  dsimp only [id_eq] at hsub
  have heq : (fun a => OracleComp.interpret
        (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n)) (handler a))
        (ProbOracleComp.lowerWith iJ (capIn a) (program a))) =
      (fun a => ProbOracleComp.lowerWith iK (r a) (m.adapt (program a))) := by
    funext a
    rw [← OracleComp.substitute_eq_interpret]
    change ProbOracleComp.simulate (handler a) (ProbOracleComp.lowerWith iJ (capIn a) (program a)) =
      ProbOracleComp.lowerWith iK (r a) (m.adapt (program a))
    rw [ProbOracleComp.lowerWith, ProbOracleComp.lowerWith, WordInterface.PortMap.adapt,
      ProbOracleComp.simulate_simulate, ProbOracleComp.simulate_simulate]
    congr 1
    funext j
    simp only [WordInterface.lowerQuery, ProbOracleComp.simulate_map, ProbOracleComp.simulate_query,
      handler, m.channelMap_channel j, m.wordMap_request j, Functor.map_map]
    congr 1
    funext w
    rw [List.take_of_length_le (hfit a (iJ.channel j) w), m.decodeReply_replyMap j]
  rwa [heq] at hsub

/-! ### Static-corruption routing (`routeCorrupt` and `corruptRouter`) -/

private def routeCorruptWordStep {n : ℕ} {ιI : Type} {I : ιI → Type}
    {In Out NetQ NetR : Type}
    (M : ℕ → Finset (Fin n) → Machine I (protocolSpec n In Out NetQ NetR))
    (iI : WordInterface I)
    (party : WordPort (Fin n × In) (Option Out)) (netPort : WordPort NetQ NetR)
    (codec : StateCodec M) (p : PPTParam n)
    (ch : (WordInterface.protocol party (WordPort.sum party netPort)).Channel)
    (w state : List Bool) : WordOracleComp iI.Channel (List Bool × List Bool) :=
  match ch with
  | .inl () =>
    if (party.queryDecoder.decode w).1 ∈ p.corrupted then
      pure (party.reply none,
        (codec p.secParam p.corrupted).enc ((codec p.secParam p.corrupted).decode state))
    else
      wordHandle M iI (WordInterface.protocol party netPort) codec p (.inl (), w) state
  | .inr () =>
    if w.headD false then
      (fun out : List Bool × List Bool => (true :: out.1, out.2)) <$>
        wordHandle M iI (WordInterface.protocol party netPort) codec p (.inr (), w.tail) state
    else if (party.queryDecoder.decode w.tail).1 ∈ p.corrupted then
      (fun out : List Bool × List Bool => (false :: out.1, out.2)) <$>
        wordHandle M iI (WordInterface.protocol party netPort) codec p (.inl (), w.tail) state
    else
      pure ((WordPort.sum party netPort).reply (.inl none),
        (codec p.secParam p.corrupted).enc ((codec p.secParam p.corrupted).decode state))

private theorem wordHandle_routeCorrupt {n : ℕ} {ιI : Type} {I : ιI → Type}
    {In Out NetQ NetR : Type}
    (M : ℕ → Finset (Fin n) → Machine I (protocolSpec n In Out NetQ NetR))
    (iI : WordInterface I)
    (party : WordPort (Fin n × In) (Option Out)) (netPort : WordPort NetQ NetR)
    (codec : StateCodec M) (p : PPTParam n)
    (ch : (WordInterface.protocol party (WordPort.sum party netPort)).Channel)
    (w state : List Bool) :
    wordHandle (fun κ C => UC.routeCorrupt C (M κ C)) iI
      (WordInterface.protocol party (WordPort.sum party netPort)) codec p (ch, w) state =
      routeCorruptWordStep M iI party netPort codec p ch w state := by
  dsimp only [routeCorruptWordStep]
  rcases ch with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · dsimp only [wordHandle, WordInterface.protocol, WordInterface.sum, WordInterface.net,
      UC.routeCorrupt]
    by_cases hmem : (party.queryDecoder.decode w).1 ∈ p.corrupted
    · simp only [hmem, ↓reduceIte, StateT.run_pure, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure, map_pure]
    · simp only [hmem, ↓reduceIte]
  · dsimp only [wordHandle, WordInterface.protocol, WordInterface.sum, WordInterface.net,
      WordPort.sum, Decoder.sum]
    cases hhd : w.headD false
    · have hdec : (if false = true then Sum.inr (netPort.queryDecoder.decode w.tail)
          else Sum.inl (party.queryDecoder.decode w.tail)) =
          Sum.inl (party.queryDecoder.decode w.tail) := rfl
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hdec]
      dsimp only [UC.routeCorrupt]
      by_cases hmem : (party.queryDecoder.decode w.tail).1 ∈ p.corrupted
      · simp only [hmem, ↓reduceIte, StateT.run_map, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_map, Functor.map_map, encSum_inl]
        rfl
      · simp only [hmem, ↓reduceIte, StateT.run_pure, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_pure, map_pure, encSum_inl]
        rfl
    · have hdec : (if true = true then Sum.inr (netPort.queryDecoder.decode w.tail)
          else Sum.inl (party.queryDecoder.decode w.tail)) =
          Sum.inr (netPort.queryDecoder.decode w.tail) := rfl
      simp only [↓reduceIte]
      rw [hdec]
      dsimp only [UC.routeCorrupt]
      simp only [StateT.run_map, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map,
        Functor.map_map, encSum_inr]
      rfl

/-- Library construction (no cited definition): lift a `PPTCertificate` through `routeCorrupt`,
preserving the state codec and adding `cert.growth p w.tail` to cover tag-stripped routed
requests. -/
@[expose] def PPTCertificate.routeCorrupt
    {n : ℕ} {ιI : Type} {I : ιI → Type} {In Out NetQ NetR : Type}
    {M : ℕ → Finset (Fin n) → Machine I (protocolSpec n In Out NetQ NetR)}
    {iI : WordInterface I}
    {party : WordPort (Fin n × In) (Option Out)} {netPort : WordPort NetQ NetR}
    (hparty : ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1)
      encBits (encFinite (Fin n)))
    (cert : PPTCertificate M iI (WordInterface.protocol party netPort)) :
    PPTCertificate (fun κ C => UC.routeCorrupt C (M κ C))
      iI (WordInterface.protocol party (WordPort.sum party netPort)) where
  codec := cert.codec
  init := cert.init
  normalize := cert.normalize
  growth p w := cert.growth p w + cert.growth p w.tail
  growth_poly := by growth_poly [cert.growth_poly]
  handle := by
    let iE := WordInterface.protocol party netPort
    let iE' := WordInterface.protocol party (WordPort.sum party netPort)
    let EIn := encHandlerCall (encPPTParam n) (encFinite iE'.Channel) encBits
    have htag : ComputableInPolyTime
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => x.2.1.1)
        EIn (encFinite iE'.Channel) := by
      dsimp only [EIn]
      unfold encHandlerCall
      fun_prop
    have hmemFin : ComputableInPolyTime
        (fun pair : Finset (Fin n) × Fin n => decide (pair.2 ∈ pair.1))
        (encPair (encFinite (Finset (Fin n))) (encFinite (Fin n))) encBool :=
      ComputableInPolyTime.of_finite _
    have hC : ComputableInPolyTime
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => x.1.corrupted)
        EIn (encFinite (Finset (Fin n))) := by
      dsimp only [EIn]
      unfold encHandlerCall
      fun_prop
    have hw : ComputableInPolyTime
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => x.2.1.2)
        EIn encBits := by
      dsimp only [EIn]
      unfold encHandlerCall
      fun_prop
    have hwt : ComputableInPolyTime
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => x.2.1.2.tail)
        EIn encBits :=
      ComputableInPolyTime.bitsTail.comp hw
    have hcorrupt : ComputableInPolyTime
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool =>
          decide ((party.queryDecoder.decode x.2.1.2).1 ∈ x.1.corrupted))
        EIn encBool :=
      hmemFin.comp (hC.prod (hparty.comp hw))
    have hcorruptTail : ComputableInPolyTime
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool =>
          decide ((party.queryDecoder.decode x.2.1.2.tail).1 ∈ x.1.corrupted))
        EIn encBool :=
      hmemFin.comp (hC.prod (hparty.comp hwt))
    have hhead : ComputableInPolyTime
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => x.2.1.2.headD false)
        EIn encBool :=
      (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hw
    have hpairNorm : ComputableInPolyTime
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => (x.1, x.2.2))
        EIn (encPair (encPPTParam n) encBits) := by
      dsimp only [EIn]
      unfold encHandlerCall
      fun_prop
    have hnorm : ComputableInPolyTime
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool =>
          (cert.codec x.1.secParam x.1.corrupted).enc
            ((cert.codec x.1.secParam x.1.corrupted).decode x.2.2))
        EIn encBits :=
      cert.normalize.comp hpairNorm
    let mkBlocked (replyWord : List Bool) :
        IsOraclePPTOn (Operation := iI.Channel) EIn (encPair encBits encBits)
          (fun x => pure (replyWord,
            (cert.codec x.1.secParam x.1.corrupted).enc
              ((cert.codec x.1.secParam x.1.corrupted).decode x.2.2))) :=
      ((ComputableInPolyTime.const replyWord).prod hnorm).isPPTOn.isOraclePPTOn
    let mkPass (ch : iE.Channel) (reqMap : List Bool → List Bool)
        (hreqMap : ComputableInPolyTime
          (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => reqMap x.2.1.2)
          EIn encBits) :
        IsOraclePPTOn (Operation := iI.Channel) EIn (encPair encBits encBits)
          (fun x => wordHandle M iI iE cert.codec x.1 (ch, reqMap x.2.1.2) x.2.2) := by
      refine cert.handle.preprocess
        (prepare := fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool =>
          (x.1, (ch, reqMap x.2.1.2), x.2.2)) ?_
      have hp : ComputableInPolyTime
          (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => x.1)
          EIn (encPPTParam n) := by
        dsimp only [EIn]; unfold encHandlerCall; fun_prop
      have hs : ComputableInPolyTime
          (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => x.2.2)
          EIn encBits := by
        dsimp only [EIn]; unfold encHandlerCall; fun_prop
      exact hp.prod (((ComputableInPolyTime.const ch).prod hreqMap).prod hs)
    let mkTagged (b : Bool) (ch : iE.Channel) :
        IsOraclePPTOn (Operation := iI.Channel) EIn (encPair encBits encBits)
          (fun x => (fun out : List Bool × List Bool => (b :: out.1, out.2)) <$>
            wordHandle M iI iE cert.codec x.1 (ch, x.2.1.2.tail) x.2.2) :=
      (mkPass ch List.tail hwt).map
        ((ComputableInPolyTime.bitsCons (ComputableInPolyTime.const b)
          (ComputableInPolyTime.fst encBits encBits)).prod
          (ComputableInPolyTime.snd encBits encBits))
    have hcases : IsOraclePPTOn (Operation := iI.Channel) EIn (encPair encBits encBits)
        (fun x =>
          routeCorruptWordStep M iI party netPort cert.codec x.1 x.2.1.1 x.2.1.2 x.2.2) := by
      refine IsOraclePPTOn.finite_cases (Operation := iI.Channel) (Tag := iE'.Channel)
        (tagEncoding := encFinite iE'.Channel)
        (tag := fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool => x.2.1.1)
        (branch := fun ch (x : PPTParam n × (iE'.Channel × List Bool) × List Bool) =>
          routeCorruptWordStep M iI party netPort cert.codec x.1 ch x.2.1.2 x.2.2)
        htag ?_
      rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
      · exact IsOraclePPTOn.ite hcorrupt (mkBlocked (party.reply none)) (mkPass (.inl ()) id hw)
      · exact IsOraclePPTOn.cond hhead (mkTagged true (.inr ()))
          (IsOraclePPTOn.ite hcorruptTail (mkTagged false (.inl ()))
            (mkBlocked ((WordPort.sum party netPort).reply (.inl none))))
    have heq :
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool =>
          routeCorruptWordStep M iI party netPort cert.codec x.1 x.2.1.1 x.2.1.2 x.2.2) =
        (fun x : PPTParam n × (iE'.Channel × List Bool) × List Bool =>
          wordHandle (fun κ C => UC.routeCorrupt C (M κ C)) iI iE' cert.codec
            x.1 x.2.1 x.2.2) := by
      funext ⟨p, ⟨ch, w⟩, state⟩
      exact (wordHandle_routeCorrupt M iI party netPort cert.codec p ch w state).symm
    rwa [heq] at hcases
  preserve p request s result hresult := by
    let s' : (M p.secParam p.corrupted).State := s
    have hres' : result ∈ OracleComp.support
        (wordHandle (fun κ C => UC.routeCorrupt C (M κ C)) iI
          (WordInterface.protocol party (WordPort.sum party netPort)) cert.codec p request
          ((cert.codec p.secParam p.corrupted).enc s')) := hresult
    suffices hgoal : result.2.length ≤
        ((cert.codec p.secParam p.corrupted).enc s').length +
          (cert.growth p request.2 + cert.growth p request.2.tail) from hgoal
    rcases request with ⟨ch, w⟩
    rw [wordHandle_routeCorrupt] at hres'
    dsimp only [routeCorruptWordStep] at hres'
    rcases ch with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · dsimp only at hres' ⊢
      by_cases hmem : (party.queryDecoder.decode w).1 ∈ p.corrupted
      · simp only [hmem, ↓reduceIte, (cert.codec p.secParam p.corrupted).decode_enc] at hres'
        have heq := OracleComp.eq_of_mem_supportWith_pure hres'
        rw [heq]
        exact Nat.le_add_right _ _
      · simp only [hmem, ↓reduceIte] at hres'
        have hle := cert.preserve p (.inl (), w) s' result hres'
        dsimp only at hle
        omega
    · dsimp only at hres' ⊢
      cases hhd : w.headD false
      · simp only [hhd, Bool.false_eq_true, ↓reduceIte] at hres'
        by_cases hmem : (party.queryDecoder.decode w.tail).1 ∈ p.corrupted
        · simp only [hmem, ↓reduceIte, OracleComp.mem_supportWith_map_iff] at hres'
          rcases hres' with ⟨out, hout, rfl⟩
          have hle := cert.preserve p (.inl (), w.tail) s' out hout
          dsimp only at hle ⊢
          omega
        · simp only [hmem, ↓reduceIte, (cert.codec p.secParam p.corrupted).decode_enc] at hres'
          have heq := OracleComp.eq_of_mem_supportWith_pure hres'
          rw [heq]
          exact Nat.le_add_right _ _
      · simp only [hhd, ↓reduceIte, OracleComp.mem_supportWith_map_iff] at hres'
        rcases hres' with ⟨out, hout, rfl⟩
        have hle := cert.preserve p (.inr (), w.tail) s' out hout
        dsimp only at hle ⊢
        omega

/-- Library infrastructure (no cited result): static-corruption routing (`routeCorrupt`) preserves
`Machine.IsPPTFamily` whenever the party port exposes the decoded party index in polynomial time
(automatic for `WordPort.party` via `WordPort.computable_partyIndex`). -/
theorem Machine.IsPPTFamily.routeCorrupt {n : ℕ} {ιI : Type} {I : ιI → Type}
    {In Out NetQ NetR : Type}
    {M : ℕ → Finset (Fin n) → Machine I (protocolSpec n In Out NetQ NetR)}
    {iI : WordInterface I}
    {party : WordPort (Fin n × In) (Option Out)} {netPort : WordPort NetQ NetR}
    (hparty : ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1)
      encBits (encFinite (Fin n)))
    (h : Machine.IsPPTFamily M iI (WordInterface.protocol party netPort)) :
    Machine.IsPPTFamily (fun κ C => UC.routeCorrupt C (M κ C))
      iI (WordInterface.protocol party (WordPort.sum party netPort)) :=
  let ⟨cert⟩ := h
  ⟨cert.routeCorrupt hparty⟩

/-- Library infrastructure (no cited result): static-corruption routing (`corruptRouter`) preserves
`Protocol.IsPPT` whenever the party port exposes the decoded party index in polynomial time
(automatic for `WordPort.party` via `WordPort.computable_partyIndex`). -/
theorem Protocol.IsPPT.corruptRouter {n : ℕ} {In Out NetQ NetR : Type}
    {π : Protocol n In Out NetQ NetR}
    {party : WordPort (Fin n × In) (Option Out)} {netPort : WordPort NetQ NetR}
    (hparty : ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1)
      encBits (encFinite (Fin n)))
    (h : π.IsPPT party netPort) :
    Protocol.IsPPT (fun κ C => UC.corruptRouter C (π κ C))
      party (WordPort.sum party netPort) :=
  Machine.IsPPTFamily.routeCorrupt hparty h

/-! ### Machine lifting (`liftRight` and `liftAdversary`) -/

/-- Library infrastructure (no cited result): lowering a right-lifted program through `iL.sum iR`
has the same `OracleComp.support` as lowering the underlying program through `iR`. -/
theorem support_lowerWith_liftRightProgram {ιL ιR α : Type}
    {L : ιL → Type} {R : ιR → Type}
    (iL : WordInterface L) (iR : WordInterface R) (limit : ℕ) (program : ProbOracleComp R α) :
    OracleComp.support
        (ProbOracleComp.lowerWith (iL.sum iR) limit (Machine.liftRightProgram L program)) =
      OracleComp.support (ProbOracleComp.lowerWith iR limit program) := by
  rw [← adapt_portMap_inr iL iR program, ProbOracleComp.lowerWith, ProbOracleComp.lowerWith,
    WordInterface.PortMap.adapt, ProbOracleComp.simulate_simulate]
  rw [ProbOracleComp.simulate, ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
    OracleComp.substitute_eq_interpret]
  unfold OracleComp.support
  rw [OracleComp.supportWith_interpret, OracleComp.supportWith_interpret]
  congr 1
  funext q
  cases q with
  | inl k => rfl
  | inr r =>
    simp only [OracleComp.sumHandler, WordInterface.PortMap.inr, ProbOracleComp.simulate_map,
      ProbOracleComp.simulate_query, WordInterface.lowerQuery, WordInterface.sum]
    ext v
    simp only [OracleComp.mem_supportWith_map_iff, ProbOracleComp.supportWith_query,
      Set.mem_univ, true_and, exists_eq_right]

private theorem wordHandle_liftRight_inl {n : ℕ} {ιL ιR ιE : Type}
    {L : ιL → Type} {R : ιR → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine R E)
    (iL : WordInterface L) (iR : WordInterface R) (iE : WordInterface E)
    (codec : StateCodec M) (p : PPTParam n) (cL : iL.Channel) (w state : List Bool) :
    wordHandle (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE) codec
        p (.inl cL, w) state =
      (fun r => (r,
        (codec p.secParam p.corrupted).enc ((codec p.secParam p.corrupted).decode state))) <$>
        ((iL.sum iR).reply (.inl (iL.decodeQuery cL w)) <$>
          ProbOracleComp.lowerWith (iL.sum iR) p.replyBound
            (ProbOracleComp.query (spec := L ⊕ₒ R) (.inl (iL.decodeQuery cL w)))) := by
  simp only [wordHandle, WordInterface.sum, Machine.liftRight, StateT.run, StateT.lift,
    ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, bind_pure_comp]
  rfl

private theorem wordHandle_liftRight_inr {n : ℕ} {ιL ιR ιE : Type}
    {L : ιL → Type} {R : ιR → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine R E)
    (iL : WordInterface L) (iR : WordInterface R) (iE : WordInterface E)
    (codec : StateCodec M) (p : PPTParam n) (cE : iE.Channel) (w state : List Bool) :
    wordHandle (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE) codec
        p (.inr cE, w) state =
      (fun result => (iE.reply (iE.decodeQuery cE w) result.1,
        (codec p.secParam p.corrupted).enc result.2)) <$>
        ProbOracleComp.lowerWith (iL.sum iR) p.replyBound
          (Machine.liftRightProgram L
            (((M p.secParam p.corrupted).handle (iE.decodeQuery cE w)).run
              ((codec p.secParam p.corrupted).decode state))) := rfl

/-- Library construction (no cited definition): lift a `PPTCertificate` through
`Machine.liftRight`, preserving the state codec and additive growth bound. -/
@[expose] def PPTCertificate.liftRight {n : ℕ} {ιL ιR ιE : Type}
    {L : ιL → Type} {R : ιR → Type} {E : ιE → Type}
    {M : ℕ → Finset (Fin n) → Machine R E}
    {iR : WordInterface R} {iE : WordInterface E}
    (iL : WordInterface L) (cert : PPTCertificate M iR iE) :
    PPTCertificate (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE) where
  codec := cert.codec
  init := cert.init
  normalize := cert.normalize
  growth := cert.growth
  growth_poly := cert.growth_poly
  handle := by
    let EIn := encHandlerCall (encPPTParam n) (encFinite (iL.sum iE).Channel) encBits
    have htag : ComputableInPolyTime
        (fun x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool => x.2.1.1)
        EIn (encFinite (iL.sum iE).Channel) := by
      dsimp only [EIn]
      unfold encHandlerCall
      fun_prop
    refine IsOraclePPTOn.finite_cases (Operation := (iL.sum iR).Channel)
      (Tag := (iL.sum iE).Channel)
      (tagEncoding := encFinite (iL.sum iE).Channel)
      (tag := fun x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool => x.2.1.1)
      (branch := fun ch (x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool) =>
        wordHandle (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE) cert.codec
          x.1 (ch, x.2.1.2) x.2.2)
      htag ?_
    let hlim : ComputableInPolyTime
        (fun x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool => x.1.replyBound)
        EIn encUnary := by
      dsimp only [EIn]; unfold encHandlerCall; fun_prop
    rintro (cL | cE)
    · have hw : ComputableInPolyTime
          (fun x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool => x.2.1.2)
          EIn encBits := by
        dsimp only [EIn]; unfold encHandlerCall; fun_prop
      have hquery : IsOraclePPTOn (Operation := (iL.sum iR).Channel) EIn encBits
          (fun x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool =>
            (iL.sum iR).reply (.inl (iL.decodeQuery cL x.2.1.2)) <$>
              ProbOracleComp.lowerWith (iL.sum iR) x.1.replyBound
                (ProbOracleComp.query (spec := L ⊕ₒ R) (.inl (iL.decodeQuery cL x.2.1.2)))) :=
        (iL.sum iR).isOraclePPTOn_lowerWith_decodeQuery
          (ComputableInPolyTime.const (Sum.inl cL)) hw hlim
      have hpost : ComputableInPolyTime
          (fun pair : (PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool) × List Bool =>
            (pair.2,
              (cert.codec pair.1.1.secParam pair.1.1.corrupted).enc
                ((cert.codec pair.1.1.secParam pair.1.1.corrupted).decode pair.1.2.2)))
          (encPair EIn encBits) (encPair encBits encBits) := by
        have hpairNorm : ComputableInPolyTime
            (fun pair : (PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool) × List Bool =>
              (pair.1.1, pair.1.2.2))
            (encPair EIn encBits) (encPair (encPPTParam n) encBits) := by
          dsimp only [EIn]; unfold encHandlerCall; fun_prop
        exact (ComputableInPolyTime.snd EIn encBits).prod (cert.normalize.comp hpairNorm)
      have hbranch := hquery.map_with
        (f := fun (x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool) r =>
          (r,
            (cert.codec x.1.secParam x.1.corrupted).enc
              ((cert.codec x.1.secParam x.1.corrupted).decode x.2.2))) hpost
      have heq :
          (fun x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool =>
            (fun r => (r,
              (cert.codec x.1.secParam x.1.corrupted).enc
                ((cert.codec x.1.secParam x.1.corrupted).decode x.2.2))) <$>
              ((iL.sum iR).reply (.inl (iL.decodeQuery cL x.2.1.2)) <$>
                ProbOracleComp.lowerWith (iL.sum iR) x.1.replyBound
                  (ProbOracleComp.query (spec := L ⊕ₒ R) (.inl (iL.decodeQuery cL x.2.1.2))))) =
          (fun x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool =>
            wordHandle (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE) cert.codec
              x.1 (.inl cL, x.2.1.2) x.2.2) := by
        funext ⟨p, ⟨_, w⟩, state⟩
        exact (wordHandle_liftRight_inl M iL iR iE cert.codec p cL w state).symm
      rwa [heq] at hbranch
    · let prog (x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool) :
          ProbOracleComp R (List Bool × List Bool) :=
        let q := iE.decodeQuery cE x.2.1.2
        (fun result => (iE.reply q result.1,
          (cert.codec x.1.secParam x.1.corrupted).enc result.2)) <$>
          (((M x.1.secParam x.1.corrupted).handle q).run
            ((cert.codec x.1.secParam x.1.corrupted).decode x.2.2))
      have hprog : IsOraclePPTOn (Operation := iR.Channel) EIn (encPair encBits encBits)
          (fun x => ProbOracleComp.lowerWith iR x.1.replyBound (prog x)) := by
        have hpre : IsOraclePPTOn (Operation := iR.Channel) EIn (encPair encBits encBits)
            (fun x => wordHandle M iR iE cert.codec x.1 (cE, x.2.1.2) x.2.2) := by
          refine cert.handle.preprocess
            (prepare := fun x : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool =>
              (x.1, (cE, x.2.1.2), x.2.2)) ?_
          have hc : ComputableInPolyTime
              (fun _ : PPTParam n × ((iL.sum iE).Channel × List Bool) × List Bool => cE)
              EIn (encFinite iE.Channel) := ComputableInPolyTime.const cE
          dsimp only [EIn]
          unfold encHandlerCall
          fun_prop
        have heq : (fun x => wordHandle M iR iE cert.codec x.1 (cE, x.2.1.2) x.2.2) =
            (fun x => ProbOracleComp.lowerWith iR x.1.replyBound (prog x)) := by
          funext x
          simp only [wordHandle, prog, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map]
        rwa [heq] at hpre
      have hadapt := WordInterface.isOraclePPTOn_lowerWith_adapt
        (WordInterface.PortMap.inr iL iR) hprog hlim
        (fun x _ w => List.length_take_le x.1.replyBound w)
      have heq : (fun x => ProbOracleComp.lowerWith (iL.sum iR) x.1.replyBound
            ((WordInterface.PortMap.inr iL iR).adapt (prog x))) =
          (fun x => wordHandle (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE)
            cert.codec x.1 (.inr cE, x.2.1.2) x.2.2) := by
        funext x
        rw [adapt_portMap_inr iL iR (prog x), wordHandle_liftRight_inr]
        simp only [prog, Machine.liftRightProgram_map, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_map]
      rwa [heq] at hadapt
  preserve p request s result hresult := by
    let s' : (M p.secParam p.corrupted).State := s
    have hres' : result ∈ OracleComp.support
        (wordHandle (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE) cert.codec
          p request ((cert.codec p.secParam p.corrupted).enc s')) := hresult
    suffices hgoal : result.2.length ≤
        ((cert.codec p.secParam p.corrupted).enc s').length + cert.growth p request.2 from hgoal
    rcases request with ⟨cL | cE, w⟩
    · rw [wordHandle_liftRight_inl, (cert.codec p.secParam p.corrupted).decode_enc,
        OracleComp.mem_supportWith_map_iff] at hres'
      rcases hres' with ⟨_, _, rfl⟩
      exact Nat.le_add_right _ _
    · rw [wordHandle_liftRight_inr, OracleComp.mem_supportWith_map_iff] at hres'
      rcases hres' with ⟨x, hx, rfl⟩
      change x ∈ OracleComp.support _ at hx
      rw [support_lowerWith_liftRightProgram iL iR] at hx
      have hmem' : (iE.reply (iE.decodeQuery cE w) x.1,
            (cert.codec p.secParam p.corrupted).enc x.2) ∈
          OracleComp.support (wordHandle M iR iE cert.codec p (cE, w)
            ((cert.codec p.secParam p.corrupted).enc s')) := by
        rw [wordHandle, OracleComp.mem_supportWith_map_iff]
        exact ⟨x, hx, rfl⟩
      exact cert.preserve p (cE, w) s' _ hmem'

/-- Library infrastructure (no cited result): lifting a strict-PPT machine family past an
arbitrary left word interface preserves `Machine.IsPPTFamily`. -/
theorem Machine.IsPPTFamily.liftRight {n : ℕ} {ιL ιR ιE : Type}
    {L : ιL → Type} {R : ιR → Type} {E : ιE → Type}
    {M : ℕ → Finset (Fin n) → Machine R E}
    {iL : WordInterface L} {iR : WordInterface R} {iE : WordInterface E}
    (h : Machine.IsPPTFamily M iR iE) :
    Machine.IsPPTFamily (fun κ C => Machine.liftRight L (M κ C))
      (iL.sum iR) (iL.sum iE) :=
  let ⟨cert⟩ := h
  ⟨cert.liftRight iL⟩

/-- Library construction (no cited definition): lift an adversary's `PPTCertificate` through
`liftAdversary`. -/
@[expose] def PPTCertificate.liftAdversary {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    {A : Adversary n AdvQ AdvR NetQ NetR}
    {netPort : WordPort NetQ NetR} {adv : WordPort AdvQ AdvR}
    (party : WordPort (Fin n × In) (Option Out))
    (cert : PPTCertificate A (WordInterface.net netPort) (WordInterface.net adv)) :
    PPTCertificate (fun κ C => UC.liftAdversary (In := In) (Out := Out) (A κ C))
      (WordInterface.protocol party netPort) (WordInterface.exec party adv) :=
  cert.liftRight (WordInterface.net party)

/-- Library infrastructure (no cited result): lifting a strict-PPT adversary past the party port
(`liftAdversary`) preserves strict PPT. -/
theorem Adversary.IsPPT.liftAdversary {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    {A : Adversary n AdvQ AdvR NetQ NetR}
    {party : WordPort (Fin n × In) (Option Out)}
    {netPort : WordPort NetQ NetR} {adv : WordPort AdvQ AdvR}
    (h : A.IsPPT netPort adv) :
    Machine.IsPPTFamily (fun κ C => UC.liftAdversary (In := In) (Out := Out) (A κ C))
      (WordInterface.protocol party netPort) (WordInterface.exec party adv) :=
  h.liftRight (iL := WordInterface.net party)

end Cslib.Crypto.Protocols.UC
