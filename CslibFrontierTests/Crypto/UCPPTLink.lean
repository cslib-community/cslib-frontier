/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.QueryBounds
import CslibFrontier.Crypto.Protocols.UC.PPT
import CslibFrontier.Crypto.Protocols.UC.PPT.Execution
public import CslibFrontier.Crypto.Protocols.UC.PPT.Link
import CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers
import CslibFrontier.Foundations.Analysis.SpecificLimits.PolyLtPow
import CslibFrontier.Languages.Probabilistic.Oracle.Support
public import CslibFrontierTests.Crypto.UCPPT

/-!
# Tests for `UC.PPT.Link`

Non-degenerate witnesses for `CslibFrontier.Crypto.Protocols.UC.PPT.Link`:

1. `Machine.IsReplyBounded` admits unbounded coin-masked growing state (`windowProtocol`,
   certified strict PPT by `windowProtocolCert` / `windowProtocol_isPPT`, returning a `κ`-bit
   prefix, and lifted via `Machine.IsReplyBounded.routeCorrupt`), while `coinStore.toProtocol`
   fails `Machine.IsReplyBounded` (`coinStore_not_isReplyBounded`).
2. `Environment.IsPPT.link` and `Machine.IsReplyBounded.liftRight` for a reply-growing adversary
   `tagAdv` linked with `advPollEnv`, plus an observable witness
   (`tagAdv_enlarged_cap_prevents_truncation`) that without an enlarged cap the reply is truncated.
3. Negative linking witness (`link_without_isReplyBounded_not_isPPT`) showing
   `Environment.IsPPT.link` fails without `Machine.IsReplyBounded`: `doubleForwardAdv` is PPT yet
   reply-unbounded, and `iterLinkEnv` is PPT, yet linking them yields a non-PPT environment via
   `IsOraclePPTOn.query_bounds`, whereas absorbing the reply-bounded `tagAdv` into `iterLinkEnv`
   stays strict PPT (`iterLinkEnv_absorbAdversary_tagAdv_isPPT`).
4. A one-query caller can read the last bit of an unrestricted honest echo using an
   auxiliary-input-dependent cap. The same criterion rejects the exponential feedback witness.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPPTLink

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.UCPPT

/-! ### 1. `IsReplyBounded` with growing state and `¬ IsReplyBounded` for `coinStore` -/

section ReplyBoundWitnesses

/-- Two-party protocol with coin-masked growing state: party `0` appends `b ^^ c`, party `1`
polls the `κ`-bit prefix, and the backdoor is a no-op. -/
@[expose] public noncomputable def windowProtocol : Protocol 2 Bool (List Bool) Unit Unit :=
  fun κ _ =>
    { State := List Bool
      init := pure []
      handle := fun
        | Sum.inl (i, b), s =>
          if i = 0 then do
            let c ← ProbOracleComp.sample (ProbComp.uniform Bool)
            pure (none, (b ^^ c) :: s)
          else pure (some (List.take κ s), s)
        | Sum.inr (), s => pure ((), s) }

/-- Strict-PPT certificate for `windowProtocol` reusing `bitsWordCodec` and
`isPPTOn_coinWriteStep`. -/
public noncomputable def windowProtocolCert :
    PPTCertificate windowProtocol WordInterface.empty
      (WordInterface.protocol coinPartyPort unitPort) where
  codec _ _ := bitsWordCodec
  init := (ComputableInPolyTime.const (encIn := encPPTParam 2) (encOut := encBits) []).isPPTOn
  handle := by
    let iP := WordInterface.protocol coinPartyPort unitPort
    let EIn := encHandlerCall (encPPTParam 2) (encFinite iP.Channel) encBits
    have htag : ComputableInPolyTime
        (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool => x.2.1.1)
        EIn (encFinite iP.Channel) := by
      unfold EIn encHandlerCall; fun_prop
    have hreqState : ComputableInPolyTime
        (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool => (x.2.1.2, x.2.2))
        EIn (encPair encBits encBits) := by
      unfold EIn encHandlerCall; fun_prop
    have hstate : ComputableInPolyTime
        (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool => x.2.2) EIn encBits := by
      unfold EIn encHandlerCall; fun_prop
    have hcond : ComputableInPolyTime
        (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool =>
          decide ((coinPartyPort.queryDecoder.decode x.2.1.2).1 = 0))
        EIn encBool :=
      (ComputableInPolyTime.of_finite (fun i : Fin 2 => decide (i = 0))).comp
        ((WordPort.computable_partyIndex coinInputPort).comp
          (by unfold EIn encHandlerCall; fun_prop))
    have hyes : IsOraclePPTOn (Operation := WordInterface.empty.Channel) EIn
        (encPair encBits encBits)
        (fun x => ProbOracleComp.sample
          ((fun c => (coinPartyPort.reply none,
            ((coinPartyPort.queryDecoder.decode x.2.1.2).2 ^^ c) :: x.2.2)) <$>
              ProbComp.uniform Bool)) :=
      (isPPTOn_coinWriteStep.preprocess hreqState).isOraclePPTOn
    have hno : IsOraclePPTOn (Operation := WordInterface.empty.Channel) EIn
        (encPair encBits encBits)
        (fun x => pure (coinPartyPort.reply (some (List.take x.1.secParam x.2.2)), x.2.2)) := by
      have htake : ComputableInPolyTime
          (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool =>
            List.take x.1.secParam x.2.2) EIn encBits :=
        ComputableInPolyTime.bitsTakeWithInput hstate (by unfold EIn encHandlerCall; fun_prop)
      have hrep : ComputableInPolyTime
          (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool =>
            coinPartyPort.reply (some (List.take x.1.secParam x.2.2))) EIn encBits :=
        (ComputableInPolyTime.of_eq (encIn := encOption encBits) (encOut := encBits)
          (f := coinPartyPort.reply) (fun _ => rfl)).comp
          (by fun_prop : ComputableInPolyTime
            (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool =>
              some (List.take x.1.secParam x.2.2)) EIn (encOption encBits))
      exact (hrep.prod hstate).isPPTOn.isOraclePPTOn
    have hnet : IsOraclePPTOn (Operation := WordInterface.empty.Channel) EIn
        (encPair encBits encBits)
        (fun x => pure (unitPort.reply (), x.2.2)) :=
      ((ComputableInPolyTime.const (unitPort.reply ())).prod hstate).isPPTOn.isOraclePPTOn
    let branch : iP.Channel → PPTParam 2 × (iP.Channel × List Bool) × List Bool →
        WordOracleComp WordInterface.empty.Channel (List Bool × List Bool) := fun c x =>
      match c with
      | .inl () =>
        if (coinPartyPort.queryDecoder.decode x.2.1.2).1 = 0 then
          ProbOracleComp.sample
            ((fun c => (coinPartyPort.reply none,
              ((coinPartyPort.queryDecoder.decode x.2.1.2).2 ^^ c) :: x.2.2)) <$>
                ProbComp.uniform Bool)
        else pure (coinPartyPort.reply (some (List.take x.1.secParam x.2.2)), x.2.2)
      | .inr () => pure (unitPort.reply (), x.2.2)
    refine (IsOraclePPTOn.finite_cases (branch := branch) htag ?_).congr fun x State oracle s => ?_
    · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
      · exact IsOraclePPTOn.ite hcond hyes hno
      · exact hnet
    · rcases x with ⟨p, ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, req⟩, sw⟩
      · by_cases hi : (coinPartyPort.queryDecoder.decode req).1 = 0
        · simp only [branch, wordHandle, windowProtocol, bitsWordCodec, WordInterface.protocol,
            WordInterface.sum, WordInterface.net, StateT.run, hi, ↓reduceIte,
            ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample,
            ProbOracleComp.simulate_pure, ProbOracleComp.sample_bind, ProbOracleComp.sample_pure,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, id_eq]; rfl
        · simp only [branch, wordHandle, windowProtocol, bitsWordCodec, WordInterface.protocol,
            WordInterface.sum, WordInterface.net, StateT.run, hi, ↓reduceIte,
            ProbOracleComp.lowerWith, ProbOracleComp.simulate_pure, map_pure, id_eq]; rfl
      · simp only [branch, wordHandle, windowProtocol, bitsWordCodec, WordInterface.protocol,
          WordInterface.sum, WordInterface.net, StateT.run, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_pure, map_pure, id_eq]; rfl
  normalize := ComputableInPolyTime.snd (encPPTParam 2) encBits
  growth _ _ := 1
  growth_poly := PolyBounded.const 1
  preserve p request s out hout := by
    let s' : List Bool := s
    rcases request with ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, req⟩
    · by_cases hi : (coinPartyPort.queryDecoder.decode req).1 = 0
      · simp only [wordHandle, windowProtocol, bitsWordCodec, WordInterface.protocol,
          WordInterface.sum, WordInterface.net, StateT.run, hi, ↓reduceIte,
          ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample,
          ProbOracleComp.simulate_pure, OracleComp.support] at hout
        rcases OracleComp.mem_supportWith_map_iff.mp hout with ⟨y, hy, rfl⟩
        rcases OracleComp.mem_supportWith_bind_iff.mp hy with ⟨c, _, hc⟩
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hc
        change (((coinPartyPort.queryDecoder.decode req).2 ^^ c) :: s').length ≤ s'.length + 1
        simp
      · simp only [wordHandle, windowProtocol, bitsWordCodec, WordInterface.protocol,
          WordInterface.sum, WordInterface.net, StateT.run, hi, ↓reduceIte,
          ProbOracleComp.lowerWith, ProbOracleComp.simulate_pure, OracleComp.support] at hout
        rcases OracleComp.mem_supportWith_map_iff.mp hout with ⟨y, hy, rfl⟩
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hy
        change s'.length ≤ s'.length + 1; omega
    · simp only [wordHandle, windowProtocol, bitsWordCodec, WordInterface.protocol,
        WordInterface.sum, WordInterface.net, StateT.run, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure, OracleComp.support] at hout
      rcases OracleComp.mem_supportWith_map_iff.mp hout with ⟨y, hy, rfl⟩
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hy
      change s'.length ≤ s'.length + 1; omega

/-- `windowProtocol` is strict PPT (`Protocol.IsPPT`). -/
public theorem windowProtocol_isPPT : windowProtocol.IsPPT coinPartyPort unitPort :=
  ⟨windowProtocolCert⟩

/-- Polling `windowProtocol` on a length-`2 * κ` state returns length `κ < 2 * κ`. -/
theorem windowProtocol_poll_shorter_than_state (κ : ℕ) (hκ : 1 ≤ κ) :
    let s : (windowProtocol κ ∅).State := List.replicate (2 * κ) true
    ProbOracleComp.runWith emptyWordOracle
        (ProbOracleComp.lowerWith WordInterface.empty 0
          (((windowProtocol κ ∅).handle (Sum.inl ((1 : Fin 2), false))).run s)) () =
      PMF.pure (((some (List.replicate κ true) : Option (List Bool)), s), ()) ∧
    (List.replicate κ true).length < s.length := by
  have hne : (1 : Fin 2) ≠ 0 := by decide
  refine ⟨?_, by simp; omega⟩
  simp only [windowProtocol, StateT.run, hne, ↓reduceIte, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_pure, ProbOracleComp.runWith_pure, List.take_replicate]
  rw [show min κ (2 * κ) = κ by omega]

/-- `windowProtocol` satisfies `Machine.IsReplyBounded` with bound `p.secParam + 1`. -/
public theorem windowProtocol_isReplyBounded :
    Machine.IsReplyBounded windowProtocol WordInterface.empty
      (WordInterface.protocol coinPartyPort unitPort) := by
  have hsec : PolyBounded (fun p : PPTParam 2 => (encPPTParam 2 p).length)
      (fun p : PPTParam 2 => p.secParam) :=
    ((by fun_prop : ComputableInPolyTime (fun p : PPTParam 2 => p.secParam)
      (encPPTParam 2) encUnary).polyBounded_length).mono fun p => by simp [encUnary_apply]
  refine ⟨fun p => p.secParam + 1, hsec.add (PolyBounded.const 1), fun p q s x hx => ?_⟩
  let s' : List Bool := s
  rcases q with ⟨i, b⟩ | ⟨⟩
  · by_cases hi : i = 0
    · simp only [windowProtocol, StateT.run, hi, ↓reduceIte, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample,
        ProbOracleComp.simulate_pure, OracleComp.support] at hx
      rcases OracleComp.mem_supportWith_bind_iff.mp hx with ⟨c, _, hc⟩
      have h1 : x.1 = none := congrArg Prod.fst (OracleComp.eq_of_mem_supportWith_pure hc)
      change (coinPartyPort.reply x.1).length ≤ p.secParam + 1
      rw [h1]; simp [coinPartyPort, WordPort.party, encOption_none]
    · simp only [windowProtocol, StateT.run, hi, ↓reduceIte, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure, OracleComp.support] at hx
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx
      change (coinPartyPort.reply (some (List.take p.secParam s'))).length ≤ p.secParam + 1
      simp only [coinPartyPort, WordPort.party, coinInputPort, encOption_some, encBits_apply,
        List.length_cons]
      have := List.length_take_le p.secParam s'; omega
  · simp only [windowProtocol, StateT.run, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_pure, OracleComp.support] at hx
    obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx
    change ([] : List Bool).length ≤ p.secParam + 1; simp

/-- Transfer of `windowProtocol_isReplyBounded` through static-corruption routing. -/
theorem windowProtocol_corruptRouter_isReplyBounded :
    Machine.IsReplyBounded (fun κ C => corruptRouter C (windowProtocol κ C)) WordInterface.empty
      (WordInterface.protocol coinPartyPort (WordPort.sum coinPartyPort unitPort)) :=
  windowProtocol_isReplyBounded.routeCorrupt

/-- `coinStore.toProtocol` is not `Machine.IsReplyBounded`: party-`1` polls echo the full state. -/
theorem coinStore_not_isReplyBounded :
    ¬ Machine.IsReplyBounded coinStore.toProtocol WordInterface.empty
      (WordInterface.protocol coinPartyPort unitPort) := by
  rintro ⟨bound, _, hle⟩
  let p : PPTParam 2 := ⟨0, 0, ∅⟩
  let s : List Bool := List.replicate (bound p + 1) true
  have hmem : ((some s : Option (List Bool)), s) ∈ OracleComp.support
      (ProbOracleComp.lowerWith WordInterface.empty p.replyBound
        (((coinStore.toProtocol p.secParam p.corrupted).handle
          (Sum.inl ((1 : Fin 2), false))).run s)) := by
    change ((some s : Option (List Bool)), s) ∈ OracleComp.support
      (ProbOracleComp.lowerWith WordInterface.empty 0
        (ProbOracleComp.sample ((coinStore.onInput (1 : Fin 2) false).run s)))
    rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_sample, ProbOracleComp.support_sample,
      coinStore_onInput_one_eval]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have hlen := hle p (Sum.inl ((1 : Fin 2), false)) s ((some s : Option (List Bool)), s) hmem
  change (coinPartyPort.reply (some s)).length ≤ bound p at hlen
  simp only [coinPartyPort, WordPort.party, coinInputPort, encOption_some, encBits_apply,
    List.length_cons, s, List.length_replicate] at hlen; omega

end ReplyBoundWitnesses

/-! ### 2. Linking witness and truncation contrast -/

section LinkWitness

/-- Stateless reply-growing adversary forwarding queries and prepending `true` to each reply. -/
private def tagAdv : Adversary 2 (List Bool) (List Bool) (List Bool) (List Bool) :=
  fun _ _ =>
    { State := PUnit
      init := pure PUnit.unit
      handle := fun q _ => (fun r => (true :: r, PUnit.unit)) <$>
        ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) q }

private def tagAdvCert :
    PPTCertificate tagAdv (WordInterface.net msgPort) (WordInterface.net msgPort) where
  codec _ _ := punitWordCodec
  init := (ComputableInPolyTime.const (encIn := encPPTParam 2) (encOut := encBits) []).isPPTOn
  handle := by
    let iN := WordInterface.net msgPort
    let EIn := encHandlerCall (encPPTParam 2) (encFinite iN.Channel) encBits
    have hq : IsOraclePPTOn EIn encBits
        (fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool =>
          iN.reply (iN.decodeQuery x.2.1.1 x.2.1.2) <$>
            ProbOracleComp.lowerWith iN x.1.replyBound
              (ProbOracleComp.query (iN.decodeQuery x.2.1.1 x.2.1.2))) := by
      refine iN.isOraclePPTOn_lowerWith_decodeQuery
        (ch := fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool => x.2.1.1)
        (word := fun x => x.2.1.2) (limit := fun x => x.1.replyBound) ?_ ?_ ?_ <;>
        (unfold EIn encHandlerCall; fun_prop)
    have hstep : ComputableInPolyTime (fun w : List Bool => (true :: w, ([] : List Bool)))
        encBits (encPair encBits encBits) :=
      (ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
        (by fun_prop : ComputableInPolyTime id encBits encBits)).prod
        (ComputableInPolyTime.const (encIn := encBits) (encOut := encBits) [])
    refine (hq.map hstep).congr fun x State oracle s => ?_
    rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
    simp only [wordHandle, tagAdv, punitWordCodec, StateT.run, ProbOracleComp.lowerWith,
      Functor.map_map]
    rfl
  normalize := ComputableInPolyTime.const (encIn := encPair (encPPTParam 2) encBits)
    (encOut := encBits) []
  growth _ _ := 0
  growth_poly := PolyBounded.const 0
  preserve _ _ _ out hout := by
    simp only [wordHandle, tagAdv, punitWordCodec, StateT.run, ProbOracleComp.lowerWith,
      OracleComp.support, OracleComp.supportWith_map, Set.mem_image] at hout
    rcases hout with ⟨_, _, rfl⟩; exact Nat.le_refl 0

/-- `tagAdv` is strict PPT (`Adversary.IsPPT`). -/
theorem tagAdv_isPPT : tagAdv.IsPPT msgPort msgPort := ⟨tagAdvCert⟩

/-- `tagAdv` is `Machine.IsReplyBounded` with bound `p.replyBound + 1`. -/
theorem tagAdv_isReplyBounded :
    Machine.IsReplyBounded tagAdv (WordInterface.net msgPort) (WordInterface.net msgPort) := by
  have hrb : PolyBounded (fun p : PPTParam 2 => (encPPTParam 2 p).length)
      (fun p : PPTParam 2 => p.replyBound) := by
    simpa only [encUnary_apply, List.length_replicate] using
      (by fun_prop : ComputableInPolyTime (fun p : PPTParam 2 => p.replyBound)
        (encPPTParam 2) encUnary).polyBounded_length
  refine ⟨fun p => p.replyBound + 1, hrb.add (PolyBounded.const 1), fun p q s x hx => ?_⟩
  simp only [tagAdv, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map,
    ProbOracleComp.simulate_query, WordInterface.lowerQuery, WordInterface.net,
    OracleComp.support] at hx
  rcases OracleComp.mem_supportWith_map_iff.mp hx with ⟨t, ht, rfl⟩
  rcases OracleComp.mem_supportWith_map_iff.mp ht with ⟨u, hu, rfl⟩
  rcases OracleComp.mem_supportWith_map_iff.mp hu with ⟨w, _, rfl⟩
  simp only [WordInterface.net, msgPort, Decoder.bits, encBits_apply,
    id_eq, List.length_cons, List.length_take]
  omega

/-- Interactive environment querying adversary `[true]` and checking `1 < r.length`. -/
private def advPollEnv : Environment 2 Bool (List Bool) (List Bool) (List Bool) :=
  fun _ _ => do let r ← ProbOracleComp.query (Sum.inr [true]); return decide (1 < r.length)

private theorem advPollEnv_isPPT : advPollEnv.IsPPT coinPartyPort msgPort := by
  let iE := WordInterface.exec coinPartyPort msgPort
  have hq : IsOraclePPTOn encEnvParam encBits fun e : EnvParam =>
      iE.reply (Sum.inr [true]) <$> ProbOracleComp.lowerWith iE e.replyBound
        (ProbOracleComp.query (spec := execSpec 2 Bool (List Bool) (List Bool) (List Bool))
          (Sum.inr [true])) :=
    iE.isOraclePPTOn_lowerWith_query (query := fun _ => Sum.inr [true])
      (limit := fun e : EnvParam => e.replyBound) (ComputableInPolyTime.const _)
      (ComputableInPolyTime.const _) (by fun_prop)
  have hlen : ComputableInPolyTime (fun w : List Bool => (msgPort.replyDecoder.decode w).length)
      encBits encUnary := by
    simpa only [encBits_apply, Function.comp_def] using
      (ComputableInPolyTime.encoding_length encBits).comp msgPort.replyDecoder.computableInPolyTime
  have hpost := (by fun_prop :
    ComputableInPolyTime (fun k : ℕ => decide (1 < k)) encUnary encBool).comp hlen
  refine (hq.map hpost).congr fun e State oracle s => ?_
  simp only [advPollEnv, iE, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery,
    WordInterface.exec, WordInterface.sum, WordInterface.net, Functor.map_map]; rfl

/-- Linking `advPollEnv` against the lifted reply-growing `tagAdv` preserves `Environment.IsPPT`. -/
theorem advPollEnv_link_tagAdv_isPPT :
    Environment.IsPPT (fun κ z => (Machine.liftRight _ (tagAdv κ {1})).link (advPollEnv κ z))
      coinPartyPort msgPort :=
  advPollEnv_isPPT.link (tagAdv_isPPT.liftAdversary)
    (tagAdv_isReplyBounded.liftRight (iL := WordInterface.net coinPartyPort)) {1}

/-- Truncation contrast: against a 1-bit oracle (`[false]`), lowering `tagAdv` at `replyBound = 1`
truncates `[true, false]` to `[true]`, whereas enlarged cap `L = 2` returns `[true, false]`. -/
theorem tagAdv_enlarged_cap_prevents_truncation :
    let oneBit : (WordInterface.net msgPort).Channel × List Bool → StateT Unit PMF (List Bool) :=
      fun _ s => PMF.pure ([false], s)
    let advOracle : (WordInterface.net msgPort).Channel × List Bool →
        StateT (PUnit × Unit) PMF (List Bool) := fun cw st =>
      (fun x => (msgPort.reply x.1.1, (x.1.2, x.2))) <$> ProbOracleComp.runWith oneBit
        (ProbOracleComp.lowerWith (WordInterface.net msgPort) 1
          (((tagAdv 0 ∅).handle (msgPort.queryDecoder.decode cw.2)).run st.1)) ()
    ProbOracleComp.runWith advOracle (ProbOracleComp.lowerWith (WordInterface.net msgPort) 1
        (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) [true]))
        (PUnit.unit, ()) ≠
      ProbOracleComp.runWith advOracle (ProbOracleComp.lowerWith (WordInterface.net msgPort) 2
        (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) [true]))
        (PUnit.unit, ()) := by
  intro oneBit advOracle
  have hq : advOracle ((WordInterface.net msgPort).channel [true],
      (WordInterface.net msgPort).request [true]) (PUnit.unit, ()) =
      PMF.pure ([true, false], (PUnit.unit, ())) := by
    change (fun x => (msgPort.reply x.1.1, (x.1.2, x.2))) <$>
        ProbOracleComp.runWith oneBit (ProbOracleComp.lowerWith (WordInterface.net msgPort) 1
          ((fun r => (true :: r, PUnit.unit)) <$>
            ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) [true])) () = _
    rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_map, ProbOracleComp.simulate_query,
      WordInterface.lowerQuery, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
    simp only [oneBit, PMF.monad_map_eq_map, PMF.pure_map, Prod.map_apply, WordInterface.net,
      msgPort, Decoder.bits, encBits_apply, id_eq, List.take_succ_cons, List.take_zero]
  have heval (k : ℕ) : ProbOracleComp.runWith advOracle (ProbOracleComp.lowerWith
      (WordInterface.net msgPort) k (ProbOracleComp.query (spec := netSpec (List Bool)
        (List Bool)) [true])) (PUnit.unit, ()) =
      PMF.pure (List.take k [true, false], (PUnit.unit, ())) := by
    rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, WordInterface.lowerQuery,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, hq,
      PMF.pure_map, PMF.pure_map]; rfl
  intro h; have h' := congrArg (fun d => d ([true], (PUnit.unit, ()))) h
  rw [heval 1, heval 2] at h'; simp [PMF.pure_apply] at h'

end LinkWitness

/-! ### 3. Negative linking witness: `Environment.IsPPT.link` fails without `IsReplyBounded` -/

section NegativeLinkWitness

/-- Adversary forwarding `w` and returning `w ++ w` (`IsPPT`, not `Machine.IsReplyBounded`). -/
private def doubleForwardAdv : Adversary 2 (List Bool) (List Bool) (List Bool) (List Bool) :=
  fun _ _ =>
    { State := PUnit
      init := pure PUnit.unit
      handle := fun w _ =>
        ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) w >>= fun _ =>
          pure (w ++ w, PUnit.unit) }

/-- `doubleForwardAdv` is strict PPT (`Adversary.IsPPT`). -/
theorem doubleForwardAdv_isPPT : doubleForwardAdv.IsPPT msgPort msgPort := by
  let iN := WordInterface.net msgPort
  let EIn := encHandlerCall (encPPTParam 2) (encFinite iN.Channel) encBits
  have hq : IsOraclePPTOn EIn encBits fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool =>
      iN.reply (iN.decodeQuery x.2.1.1 x.2.1.2) <$> ProbOracleComp.lowerWith iN x.1.replyBound
        (ProbOracleComp.query (iN.decodeQuery x.2.1.1 x.2.1.2)) := by
    refine iN.isOraclePPTOn_lowerWith_decodeQuery
      (ch := fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool => x.2.1.1)
      (word := fun x => x.2.1.2) (limit := fun x => x.1.replyBound) ?_ ?_ ?_ <;>
      (unfold EIn encHandlerCall; fun_prop)
  have hword : ComputableInPolyTime
      (fun p : (PPTParam 2 × (iN.Channel × List Bool) × List Bool) × List Bool => p.1.2.1.2)
      (encPair EIn encBits) encBits := by
    unfold EIn encHandlerCall; fun_prop
  have hstep : ComputableInPolyTime
      (fun p : (PPTParam 2 × (iN.Channel × List Bool) × List Bool) × List Bool =>
        (p.1.2.1.2 ++ p.1.2.1.2, ([] : List Bool)))
      (encPair EIn encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.bitsAppend hword hword).prod
      (ComputableInPolyTime.const (encIn := encPair EIn encBits) (encOut := encBits) [])
  refine ⟨{
    codec := fun _ _ => punitWordCodec
    init := (ComputableInPolyTime.const (encIn := encPPTParam 2) (encOut := encBits) []).isPPTOn
    handle := by
      refine (hq.keep_input.map hstep).congr fun x State oracle s => ?_
      rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
      simp only [wordHandle, doubleForwardAdv, punitWordCodec, StateT.run, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pure, ProbOracleComp.runWith_bind,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      rfl
    normalize := ComputableInPolyTime.const (encIn := encPair (encPPTParam 2) encBits)
      (encOut := encBits) []
    growth _ _ := 0
    growth_poly := PolyBounded.const 0
    preserve _ _ _ out hout := by
      simp only [wordHandle, doubleForwardAdv, punitWordCodec, StateT.run, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pure, OracleComp.support] at hout
      rcases OracleComp.mem_supportWith_map_iff.mp hout with ⟨⟨_, _⟩, _, rfl⟩
      exact Nat.le_refl 0 }⟩

/-- `doubleForwardAdv` is not `Machine.IsReplyBounded` (`w ↦ w ++ w`). -/
theorem doubleForwardAdv_not_isReplyBounded :
    ¬ Machine.IsReplyBounded doubleForwardAdv
      (WordInterface.net msgPort) (WordInterface.net msgPort) := by
  rintro ⟨bound, _, hle⟩
  let p : PPTParam 2 := ⟨0, 0, ∅⟩
  let w : List Bool := List.replicate (bound p + 1) true
  have hmem : (w ++ w, PUnit.unit) ∈ OracleComp.support (ProbOracleComp.lowerWith
      (WordInterface.net msgPort) p.replyBound
      (((doubleForwardAdv 0 ∅).handle w).run PUnit.unit)) := by
    simp only [doubleForwardAdv, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
      ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery,
      OracleComp.support]
    refine OracleComp.mem_supportWith_bind_iff.mpr
      ⟨[], OracleComp.mem_supportWith_map_iff.mpr
        ⟨[], OracleComp.mem_supportWith_map_iff.mpr ⟨[], by simp, rfl⟩,
          by simp [WordInterface.net, msgPort, Decoder.bits]⟩,
        by simp⟩
  have hlen := hle p w PUnit.unit (w ++ w, PUnit.unit) hmem
  simp only [WordInterface.net, msgPort, encBits_apply, List.length_append, w,
    List.length_replicate] at hlen; omega

/-- Environment iterating `κ + 1` sequential adversary queries starting from `[true]`. -/
private def iterLinkEnv : Environment 2 Bool (List Bool) (List Bool) (List Bool) :=
  fun κ _ => (fun _ => true) <$>
    OracleComp.iterate (κ + 1) (fun w => ProbOracleComp.query
      (spec := execSpec 2 Bool (List Bool) (List Bool) (List Bool)) (Sum.inr w)) [true]

/-- `iterLinkEnv` is strict PPT (`Environment.IsPPT`). -/
theorem iterLinkEnv_isPPT : iterLinkEnv.IsPPT coinPartyPort msgPort := by
  let iE := WordInterface.exec coinPartyPort msgPort
  have hrc : ComputableInPolyTime (fun e : EnvParam => e.replyBound) encEnvParam encUnary := by
    fun_prop
  have hq0 := iE.isOraclePPTOn_lowerWith_query
    (query := fun pair : EnvParam × List Bool => Sum.inr pair.2)
    (limit := fun pair => pair.1.replyBound)
    (ComputableInPolyTime.const (Sum.inr () : iE.Channel))
    (ComputableInPolyTime.snd encEnvParam encBits)
    (hrc.comp (ComputableInPolyTime.fst encEnvParam encBits))
  have hloop : IsOraclePPTOn encEnvParam encBits fun e : EnvParam =>
      OracleComp.iterate (e.secParam + 1)
        (fun w => ProbOracleComp.lowerWith iE e.replyBound
          (ProbOracleComp.query (spec := execSpec 2 Bool (List Bool) (List Bool) (List Bool))
            (Sum.inr w))) [true] := by
    have hcnt : ComputableInPolyTime (fun e : EnvParam => e.secParam + 1) encEnvParam encUnary :=
      by fun_prop
    refine IsOraclePPTOn.iterateWith_of_bounded_growth hcnt
      (ComputableInPolyTime.const (encIn := encEnvParam) (encOut := encBits) [true])
      (hq0.congr fun pair State oracle s => by
        simp only [iE, ProbOracleComp.lowerWith, ProbOracleComp.simulate_query,
          WordInterface.lowerQuery, WordInterface.exec, WordInterface.sum, WordInterface.net,
          msgPort, Decoder.bits, encBits_apply, id_eq]
        rfl)
      (by simpa only [encUnary_apply, List.length_replicate] using hrc.polyBounded_length)
      fun e state next hnext => ?_
    simp only [iE, ProbOracleComp.lowerWith, ProbOracleComp.simulate_query,
      WordInterface.lowerQuery, WordInterface.exec, WordInterface.sum, WordInterface.net,
      msgPort, Decoder.bits, encBits_apply, id_eq] at hnext
    rcases OracleComp.mem_supportWith_map_iff.mp hnext with ⟨t, ht, rfl⟩
    rcases OracleComp.mem_supportWith_map_iff.mp ht with ⟨w, _, rfl⟩
    simp only [encBits_apply, id_eq, List.length_take]; omega
  refine (hloop.map (ComputableInPolyTime.const (encIn := encBits) (encOut := encBool)
    true)).congr fun e State oracle s => ?_
  have hl : ProbOracleComp.lowerWith iE e.replyBound (iterLinkEnv e.secParam e.aux) =
      (fun _ => true) <$> OracleComp.iterate (e.secParam + 1)
        (fun w => ProbOracleComp.lowerWith iE e.replyBound (ProbOracleComp.query
          (spec := execSpec 2 Bool (List Bool) (List Bool) (List Bool)) (Sum.inr w))) [true] := by
    rw [iterLinkEnv, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map, ProbOracleComp.simulate,
      OracleComp.substitute_eq_interpret, OracleComp.interpret_iterate]; rfl
  rw [hl]

private theorem exists_poly_lt_two_pow (c d : ℕ) : ∃ κ, c * (κ + 1) ^ d < 2 ^ κ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_mul_add_one_pow_lt_pow (c : ℝ) d (by norm_num : (1 : ℝ) < 2))
  refine ⟨N, ?_⟩
  exact_mod_cast hN N le_rfl

private theorem queriesSatisfy_bind_right {ι : Type} {spec : ι → Type} {α β : Type}
    {p : ι → Prop} {prog : OracleComp spec α} {cont : α → OracleComp spec β}
    (h : OracleComp.QueriesSatisfy p (prog >>= cont)) {x : α}
    (hx : x ∈ OracleComp.support prog) :
    OracleComp.QueriesSatisfy p (cont x) := by
  induction prog with
  | pure a => cases hx; exact h
  | liftBind q cont' ih =>
    rcases Set.mem_iUnion₂.mp hx with ⟨a, _, ha⟩
    exact ih a ((OracleComp.QueriesSatisfy.liftBind_iff.mp h).2 a) ha

/-- Negative linking witness: `Environment.IsPPT.link` fails without `Machine.IsReplyBounded`.
Both `iterLinkEnv` (`iterLinkEnv_isPPT`) and `liftAdversary doubleForwardAdv`
(`doubleForwardAdv_isPPT.liftAdversary`) are strict PPT, yet linking them issues an external
query of length `2 ^ κ`, contradicting `IsOraclePPTOn.query_bounds`. -/
theorem link_without_isReplyBounded_not_isPPT :
    ¬ Environment.IsPPT
      (fun κ z => (liftAdversary (In := Bool) (Out := List Bool) (doubleForwardAdv κ ∅)).link
        (iterLinkEnv κ z))
      coinPartyPort msgPort := by
  intro hLink
  let iE := WordInterface.exec coinPartyPort msgPort
  obtain ⟨c, d, hqb⟩ := IsOraclePPTOn.query_bounds hLink
  have hp : ComputableInPolyTime (fun κ : ℕ => (⟨κ, 0, []⟩ : EnvParam)) encUnary encEnvParam := by
    have : ComputableInPolyTime (fun _ : ℕ => ([] : List Bool)) encUnary encBits :=
      ComputableInPolyTime.const []
    fun_prop
  obtain ⟨cp, dp, hcp⟩ := hp.polyBounded_length.exists_le
  obtain ⟨κ, hκ⟩ := exists_poly_lt_two_pow (c * (cp + 1 + 1) ^ d) (dp * d)
  let e : EnvParam := ⟨κ, 0, []⟩
  have heLen : (encEnvParam e).length + 1 ≤ (cp + 1 + 1) * (κ + 1) ^ dp := by
    have h1 : (encEnvParam e).length ≤ cp * (κ + 1) ^ dp := by
      simpa only [encUnary_apply, List.length_replicate] using hcp κ
    have hpow := Nat.one_le_pow dp (κ + 1) (Nat.succ_pos κ)
    calc (encEnvParam e).length + 1 ≤ cp * (κ + 1) ^ dp + (κ + 1) ^ dp :=
        Nat.add_le_add h1 hpow
      _ ≤ (cp + 1 + 1) * (κ + 1) ^ dp := by simp [Nat.add_mul]
  have hpoly : c * ((encEnvParam e).length + 1) ^ d ≤
      c * (cp + 1 + 1) ^ d * (κ + 1) ^ (dp * d) := by
    calc c * ((encEnvParam e).length + 1) ^ d
        ≤ c * ((cp + 1 + 1) * (κ + 1) ^ dp) ^ d :=
          Nat.mul_le_mul_left c (Nat.pow_le_pow_left heLen d)
      _ = c * (cp + 1 + 1) ^ d * (κ + 1) ^ (dp * d) := by
          rw [mul_pow, ← pow_mul, mul_assoc]
  let M := liftAdversary (n := 2) (In := Bool) (Out := List Bool) (doubleForwardAdv κ ∅)
  have hmemIter : ∀ k (w : List Bool),
      (Nat.iterate (fun u => u ++ u) k w, (PUnit.unit : M.State)) ∈
        OracleComp.support (ProbOracleComp.lowerWith iE 0
          (M.runFrom (OracleComp.iterate k (fun u => ProbOracleComp.query
            (spec := execSpec 2 Bool (List Bool) (List Bool) (List Bool)) (Sum.inr u)) w)
            PUnit.unit)) := by
    intro k
    induction k with
    | zero =>
      intro w
      dsimp only [M, liftAdversary, Machine.liftRight, doubleForwardAdv]
      simp only [OracleComp.support, ProbOracleComp.lowerWith]
      rfl
    | succ k ih =>
      intro w
      dsimp only [M, liftAdversary, Machine.liftRight, doubleForwardAdv] at ih ⊢
      rw [OracleComp.iterate_succ, Machine.runFrom_bind]
      simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind]
      refine OracleComp.mem_supportWith_bind_iff.mpr
        ⟨(Nat.iterate (fun u => u ++ u) k w, PUnit.unit), ih w, ?_⟩
      rw [Machine.runFrom_query]
      simp only [StateT.run, Machine.liftRightProgram_bind, Machine.liftRightProgram_query,
        ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query, WordInterface.lowerQuery]
      refine OracleComp.mem_supportWith_bind_iff.mpr
        ⟨[], OracleComp.mem_supportWith_map_iff.mpr
          ⟨[], OracleComp.mem_supportWith_map_iff.mpr ⟨[], by simp, rfl⟩,
            by simp [iE, WordInterface.sum, WordInterface.net, msgPort, Decoder.bits]⟩,
          by simp [Function.iterate_succ_apply']⟩
  have hqsat := (hqb e).2
  change OracleComp.QueriesSatisfy _ (ProbOracleComp.lowerWith iE 0
    (ProbOracleComp.sample (pure (PUnit.unit : M.State)) >>= fun s =>
      Prod.fst <$> M.runFrom (iterLinkEnv κ []) s)) at hqsat
  simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind] at hqsat
  have h1 := queriesSatisfy_bind_right hqsat (x := (PUnit.unit : M.State)) (by
    rw [ProbOracleComp.simulate_sample]; simp [OracleComp.support])
  dsimp only [M, liftAdversary, Machine.liftRight, doubleForwardAdv] at h1
  rw [ProbOracleComp.simulate_map, OracleComp.queriesSatisfy_map_iff, ← ProbOracleComp.lowerWith,
    iterLinkEnv, Machine.runFrom_map, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map,
    OracleComp.queriesSatisfy_map_iff, ← ProbOracleComp.lowerWith, OracleComp.iterate_succ,
    Machine.runFrom_bind, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ← ProbOracleComp.lowerWith] at h1
  have h2 := queriesSatisfy_bind_right h1
    (x := (Nat.iterate (fun u => u ++ u) κ [true], (PUnit.unit : M.State))) (hmemIter κ [true])
  dsimp only [M, liftAdversary, Machine.liftRight, doubleForwardAdv] at h2
  rw [Machine.runFrom_query] at h2
  simp only [StateT.run, Machine.liftRightProgram_bind, Machine.liftRightProgram_query,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query, WordInterface.lowerQuery] at h2
  have hqlen := (OracleComp.QueriesSatisfy.liftBind_iff.mp h2).1
  have h2pow : ∀ k (w : List Bool),
      (Nat.iterate (fun u => u ++ u) k w).length = 2 ^ k * w.length := by
    intro k w; induction k generalizing w with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply, ih (w ++ w), List.length_append, pow_succ]; ring
  have hlen : (Nat.iterate (fun u => u ++ u) κ [true]).length = 2 ^ κ := by
    simpa using h2pow κ [true]
  simp only [iE, WordInterface.exec, WordInterface.sum, WordInterface.net, msgPort, Sum.elim_inr,
    encBits_apply, hlen] at hqlen
  exact Nat.lt_irrefl _ ((hqlen.trans hpoly).trans_lt hκ)

/-- Contrast with `link_without_isReplyBounded_not_isPPT`: absorbing the reply-bounded `tagAdv`
into the same `iterLinkEnv` stays strict PPT. -/
theorem iterLinkEnv_absorbAdversary_tagAdv_isPPT :
    (absorbAdversary {1} tagAdv iterLinkEnv).IsPPT coinPartyPort msgPort :=
  iterLinkEnv_isPPT.absorbAdversary tagAdv_isPPT tagAdv_isReplyBounded {1}

section ReachableReplyTests

private def echoPartyPort : WordPort (Fin 2 × List Bool) (Option (List Bool)) :=
  WordPort.party msgPort

/-- Honest parties copy the entire input back to the caller. No network query is issued. -/
private def honestWordEcho : Protocol 2 (List Bool) (List Bool) Unit Unit := fun _ _ =>
  { State := PUnit
    init := pure PUnit.unit
    handle := fun
      | Sum.inl (_, w), _ => pure (some w, PUnit.unit)
      | Sum.inr (), _ => pure ((), PUnit.unit) }

private theorem honestWordEcho_isPPT : honestWordEcho.IsPPT echoPartyPort unitPort := by
  let iP := WordInterface.protocol echoPartyPort unitPort
  let EIn := encHandlerCall (encPPTParam 2) (encFinite iP.Channel) encBits
  have hw : ComputableInPolyTime
      (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool => x.2.1.2)
      EIn encBits := by unfold EIn encHandlerCall; fun_prop
  have hreq : ComputableInPolyTime
      (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool =>
        (echoPartyPort.queryDecoder.decode x.2.1.2).2) EIn encBits :=
    ((ComputableInPolyTime.snd (encFinEnum (Fin 2)) encBits).comp
      echoPartyPort.queryDecoder.computableInPolyTime).comp hw
  have hrep : ComputableInPolyTime
      (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool =>
        echoPartyPort.reply (some (echoPartyPort.queryDecoder.decode x.2.1.2).2)) EIn encBits :=
    (ComputableInPolyTime.of_eq (encIn := encOption encBits) (encOut := encBits)
      (f := echoPartyPort.reply) (fun _ => rfl)).comp
      ((ComputableInPolyTime.optionSome encBits).comp hreq)
  let branch : iP.Channel → PPTParam 2 × (iP.Channel × List Bool) × List Bool →
      WordOracleComp WordInterface.empty.Channel (List Bool × List Bool) := fun c x =>
    match c with
    | .inl () => pure (echoPartyPort.reply (some (echoPartyPort.queryDecoder.decode x.2.1.2).2), [])
    | .inr () => pure (unitPort.reply (), [])
  refine ⟨{
    codec := fun _ _ => punitWordCodec
    init := (ComputableInPolyTime.const (encIn := encPPTParam 2) (encOut := encBits) []).isPPTOn
    handle := by
      have htag : ComputableInPolyTime
          (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool => x.2.1.1)
          EIn (encFinite iP.Channel) := by unfold EIn encHandlerCall; fun_prop
      refine (IsOraclePPTOn.finite_cases (branch := branch) htag ?_).congr
        fun x State oracle s => ?_
      · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
        · exact (hrep.prod (ComputableInPolyTime.const
            (encIn := EIn) (encOut := encBits) [])).isPPTOn.isOraclePPTOn
        · exact (ComputableInPolyTime.const (encIn := EIn) (encOut := encPair encBits encBits)
            (unitPort.reply (), [])).isPPTOn.isOraclePPTOn
      · rcases x with ⟨p, ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, req⟩, sw⟩ <;>
          simp only [branch, wordHandle, honestWordEcho, punitWordCodec, WordInterface.protocol,
            WordInterface.sum, WordInterface.net, StateT.run, ProbOracleComp.lowerWith,
            ProbOracleComp.simulate_pure, map_pure] <;> rfl
    normalize := ComputableInPolyTime.const (encIn := encPair (encPPTParam 2) encBits)
      (encOut := encBits) []
    growth _ _ := 0
    growth_poly := PolyBounded.const 0
    preserve p request s out hout := by
      rcases OracleComp.mem_supportWith_map_iff.mp hout with ⟨x, _, rfl⟩
      exact Nat.le_refl 0 }⟩

private theorem honestWordEcho_not_isReplyBounded :
    ¬ Machine.IsReplyBounded honestWordEcho WordInterface.empty
        (WordInterface.protocol echoPartyPort unitPort) := by
  rintro ⟨bound, _, h⟩
  let p : PPTParam 2 := ⟨0, 0, ∅⟩
  let w := List.replicate (bound p + 1) true
  have hmem : (some w, PUnit.unit) ∈ OracleComp.support
      (ProbOracleComp.lowerWith WordInterface.empty p.replyBound
        (((honestWordEcho 0 ∅).handle (Sum.inl ((0 : Fin 2), w))).run PUnit.unit)) := by
    simp [honestWordEcho, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_pure,
      OracleComp.support]
    rfl
  have hlen := h p (Sum.inl ((0 : Fin 2), w)) PUnit.unit (some w, PUnit.unit) hmem
  change (echoPartyPort.reply (some w)).length ≤ bound p at hlen
  simp only [echoPartyPort, WordPort.party, msgPort, encOption_some, encBits_apply,
    List.length_cons, w, List.length_replicate] at hlen
  omega

/-- Read the last payload bit after removing the option tag, with false for an empty payload. -/
private def lastEchoBit (w : List Bool) : Bool := w.tail.reverse.headD false

private def readAuxEcho : Environment 2 (List Bool) (List Bool) Unit Unit :=
  fun _ z => do
    let r ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), z))
    return lastEchoBit (echoPartyPort.reply r)

private theorem readAuxEcho_link_answer (κ : ℕ) (z : List Bool) :
    (honestWordEcho κ ∅).link (readAuxEcho κ z) = pure (z.reverse.headD false) := by
  simp [Machine.link, readAuxEcho, honestWordEcho, StateT.run, lastEchoBit,
    echoPartyPort, WordPort.party, msgPort, encOption_some, encBits_apply]

private theorem readAuxEcho_isPPT : readAuxEcho.IsPPT echoPartyPort unitPort := by
  let iE := WordInterface.exec echoPartyPort unitPort
  let query : EnvParam → (Fin 2 × List Bool) ⊕ Unit :=
    fun e => Sum.inl ((0 : Fin 2), e.aux)
  have hpair : ComputableInPolyTime (fun e : EnvParam => ((0 : Fin 2), e.aux))
      encEnvParam echoPartyPort.query :=
    (ComputableInPolyTime.const (encIn := encEnvParam) (encOut := encFinEnum (Fin 2))
      (0 : Fin 2)).prod (by fun_prop : ComputableInPolyTime EnvParam.aux encEnvParam encBits)
  have hreq : ComputableInPolyTime (fun e => iE.request (query e)) encEnvParam encBits :=
    (ComputableInPolyTime.of_eq (encIn := echoPartyPort.query) (encOut := encBits)
      (f := echoPartyPort.query) (fun _ => rfl)).comp hpair
  have hq := iE.isOraclePPTOn_lowerWith_query (query := query) (limit := EnvParam.replyBound)
    (ComputableInPolyTime.const (Sum.inl () : iE.Channel)) hreq (by fun_prop)
  have hpost : ComputableInPolyTime lastEchoBit encBits encBool :=
    (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp
      (ComputableInPolyTime.bitsReverse.comp ComputableInPolyTime.bitsTail)
  refine (hq.map hpost).congr fun e State oracle s => ?_
  simp only [readAuxEcho, query, iE, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery,
    WordInterface.exec, WordInterface.sum, WordInterface.net, Functor.map_map]
  rfl

/-- The one-bit option tag followed by the auxiliary input is the longest reachable reply.
The original machine-level cap fails already at fixed security parameter and external cap zero. -/
private theorem readAuxEcho_link_isOraclePPT :
    IsOraclePPTOn (Operation := WordInterface.empty.Channel) encEnvParam encBool
      (fun e : EnvParam => ProbOracleComp.lowerWith WordInterface.empty e.replyBound
        ((honestWordEcho e.secParam ∅).link (readAuxEcho e.secParam e.aux))) := by
  have hlen : ComputableInPolyTime (fun e : EnvParam => e.aux.length) encEnvParam encUnary := by
    simpa only [encBits_apply, Function.comp_def] using
      (ComputableInPolyTime.encoding_length encBits).comp
        (by fun_prop : ComputableInPolyTime EnvParam.aux encEnvParam encBits)
  have hcap : ComputableInPolyTime (fun e : EnvParam => e.aux.length + 1) encEnvParam encUnary :=
    by fun_prop
  apply readAuxEcho_isPPT.isOraclePPTOn_lowerWith_link_of_reachable
    honestWordEcho_isPPT ∅ (fun e => e.aux.length + 1) hcap
  intro e State oracle sO s0 _
  apply RepliesFitOn.query
  · intro x hx
    simp only [honestWordEcho, StateT.run, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_pure, ProbOracleComp.runWith_pure] at hx
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
    change (echoPartyPort.reply (some e.aux)).length ≤ e.aux.length + 1
    simp [echoPartyPort, WordPort.party, msgPort, encOption_some, encBits_apply]
  · intro x _
    exact .pure _ _ _

/-- The upstream observable exponential transcript excludes every computable polynomial
reachable cap for this particular caller and machine, even though each separately is PPT. -/
private theorem no_computable_reachable_cap_for_doubleForward (cap : EnvParam → ℕ)
    (hcap : ComputableInPolyTime cap encEnvParam encUnary) :
    ¬ ∀ (e : EnvParam) (State : Type)
        (oracle : (WordInterface.exec coinPartyPort msgPort).Channel × List Bool →
          StateT State PMF (List Bool)) (sO : State)
        (s0 : (liftAdversary (In := Bool) (Out := List Bool)
          (doubleForwardAdv e.secParam ∅)).State),
        s0 ∈ (liftAdversary (In := Bool) (Out := List Bool)
          (doubleForwardAdv e.secParam ∅)).init.eval.support →
        RepliesFitOn (liftAdversary (In := Bool) (Out := List Bool) (doubleForwardAdv e.secParam ∅))
          (WordInterface.exec coinPartyPort msgPort) (WordInterface.exec coinPartyPort msgPort)
          e.replyBound (cap e) oracle (iterLinkEnv e.secParam e.aux) s0 sO := by
  intro hfit
  exact link_without_isReplyBounded_not_isPPT
    (iterLinkEnv_isPPT.isOraclePPTOn_lowerWith_link_of_reachable
      doubleForwardAdv_isPPT.liftAdversary ∅ cap hcap hfit)

end ReachableReplyTests

end NegativeLinkWitness

end CslibFrontierTests.Crypto.UCPPTLink
