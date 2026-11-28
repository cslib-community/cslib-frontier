/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Protocols.UC.Execution
public import CslibFrontier.Crypto.Protocols.UC.PPT
import CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers
import CslibFrontierTests.Crypto.UCPPT

/-!
# Tests for `UC.PPT.Wrappers`

Non-degenerate witnesses for `CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers`:

1. Length-changing `PortMap` witness (`prependFalseMap`): a strict-PPT adapter with `replyMap`
   growing words by `1` bit (`w ↦ false :: w`) and distinct `r = 2` vs `capIn = 3`. Against an
   overlong `[true, true, true]` reply, the adapted computation evaluates to `[false, true, true]`,
   sensitive to taking the `r = 2` outer prefix before translation (`≠ [false, true]` and
   `≠ [false, true, true, true]`).
2. `corruptRouter` over the shared `coinStore` protocol from `UCPPT`: blocked environment inputs
   at corrupted party `1` drop without mutating state, adversary-routed inputs to party `1` and
   honest party-`0` inputs reach `coinStore`, an adversary poll returns `Sum.inl (some s)`, and
   `Protocol.IsPPT.corruptRouter` certifies the routed protocol via
   `WordPort.computable_partyIndex`.
3. `logAdv` and `liftAdversary`: a stateful unary-counter adversary forwarding `List Bool` queries
   is certified via `WordInterface.isOraclePPTOn_lowerWith_decodeQuery`, lifted via
   `Adversary.IsPPT.liftAdversary`, and evaluated on an off-image state word `[false]` to confirm
   left-channel forwarding and state-word normalization.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPPTWrappers

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.UCPPT

/-- Unary `WordCodec` for `ℕ`, shared by counter-bearing test fixtures. -/
@[expose] public def unaryCodec : WordCodec ℕ where
  enc := encUnary
  decode := Decoder.unary.decode
  decode_enc := Decoder.unary.decode_enc

/-- Shared `normalize` witness for `unaryCodec`. -/
public theorem computable_normalize_unary (n : ℕ) :
    ComputableInPolyTime
      (fun x : PPTParam n × List Bool => unaryCodec.enc (unaryCodec.decode x.2))
      (encPair (encPPTParam n) encBits) encBits :=
  (ComputableInPolyTime.of_eq (encIn := encUnary) (encOut := encBits) (fun _ => rfl)).comp
    (Decoder.unary.computableInPolyTime.comp (ComputableInPolyTime.snd _ _))

/-- Shared handler step for unary-counter forwarding machines (`logAdvCert`, `relayHybridCert`):
forwards the decoded request word on channel `cN` of `iN` and increments the unary state word. -/
public theorem isOraclePPTOn_forwardAndIncUnary {n : ℕ} {ι : Type} {I : ι → Type}
    {chOut : Type} [Finite chOut] (iN : WordInterface I) (cN : iN.Channel) :
    IsOraclePPTOn
      (encHandlerCall (encPPTParam n) (encFinite chOut) encBits)
      (encPair encBits encBits)
      (fun x : PPTParam n × (chOut × List Bool) × List Bool =>
        (fun r => (r, encUnary (Decoder.unary.decode x.2.2 + 1))) <$>
          (iN.reply (iN.decodeQuery cN x.2.1.2) <$>
            ProbOracleComp.lowerWith iN x.1.replyBound
              (ProbOracleComp.query (iN.decodeQuery cN x.2.1.2)))) := by
  let EIn := encHandlerCall (encPPTParam n) (encFinite chOut) encBits
  have hq : IsOraclePPTOn EIn encBits
      (fun x : PPTParam n × (chOut × List Bool) × List Bool =>
        iN.reply (iN.decodeQuery cN x.2.1.2) <$>
          ProbOracleComp.lowerWith iN x.1.replyBound
            (ProbOracleComp.query (iN.decodeQuery cN x.2.1.2))) :=
    iN.isOraclePPTOn_lowerWith_decodeQuery (ComputableInPolyTime.const cN)
      (by unfold EIn encHandlerCall; fun_prop) (by unfold EIn encHandlerCall; fun_prop)
  have hsucc : ComputableInPolyTime
      (fun pair : (PPTParam n × (chOut × List Bool) × List Bool) × List Bool =>
        (pair.2, encUnary (Decoder.unary.decode pair.1.2.2 + 1)))
      (encPair EIn encBits) (encPair encBits encBits) := by
    have hsw : ComputableInPolyTime
        (fun pair : (PPTParam n × (chOut × List Bool) × List Bool) × List Bool =>
          Decoder.unary.decode pair.1.2.2)
        (encPair EIn encBits) encUnary := by
      refine Decoder.unary.computableInPolyTime.comp ?_
      unfold EIn encHandlerCall; fun_prop
    have hinc := (ComputableInPolyTime.of_eq (encIn := encUnary) (encOut := encBits)
      (fun _ => rfl)).comp
      (ComputableInPolyTime.unary_add.comp (hsw.prod (ComputableInPolyTime.const 1)))
    exact (ComputableInPolyTime.snd EIn encBits).prod hinc
  exact (hq.keep_input.map hsucc).congr fun x State oracle s => by
    simp only [ProbOracleComp.runWith_map, PMF.map_comp, Function.comp_def, Prod.map, id_eq]

/-! ### 1. Length-changing `PortMap` adapter witness -/

section LengthChangingAdapterWitness

private def prependFalseMap :
    WordInterface.PortMap (WordInterface.net msgPort) (WordInterface.net msgPort) where
  queryMap := id
  replyBack _ r := false :: r
  channelMap := id
  wordMap _ w := w
  replyMap _ w := false :: w
  channelMap_channel _ := rfl
  wordMap_request _ := rfl
  decodeReply_replyMap _ _ := rfl
  wordMap_poly := ComputableInPolyTime.snd (encFinite (WordInterface.net msgPort).Channel) encBits
  replyMap_poly := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false)
    (ComputableInPolyTime.snd (encFinite (WordInterface.net msgPort).Channel) encBits)

private noncomputable def tripleOracle :
    (WordInterface.net msgPort).Channel × List Bool → StateT Unit PMF (List Bool)
  | _, s => PMF.pure ([true, true, true], s)

/-- `WordInterface.isOraclePPTOn_lowerWith_adapt` certifies `prependFalseMap.adapt` at `r = 2`
from an inner certificate at `capIn = 3` (`r ≠ capIn`). -/
theorem prependFalseMap_adapt_isOraclePPTOn :
    IsOraclePPTOn encUnit encBits (fun _ : Unit =>
      ProbOracleComp.lowerWith (WordInterface.net msgPort) 2
        (prependFalseMap.adapt
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) []))) := by
  have hinner : IsOraclePPTOn encUnit encBits (fun _ : Unit =>
      ProbOracleComp.lowerWith (WordInterface.net msgPort) 3
        (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) [])) := by
    have hq := (WordInterface.net msgPort).isOraclePPTOn_lowerWith_query
      (input := encUnit) (query := fun _ : Unit => ([] : List Bool)) (limit := fun _ => 3)
      (ComputableInPolyTime.const ()) (ComputableInPolyTime.const []) (ComputableInPolyTime.const 3)
    exact hq.congr fun _ State oracle s => rfl
  refine WordInterface.isOraclePPTOn_lowerWith_adapt prependFalseMap hinner
    (ComputableInPolyTime.const 2) fun _ _ w => ?_
  simp only [prependFalseMap, List.length_cons]
  have hlen : (List.take 2 w).length ≤ 2 := List.length_take_le 2 w
  omega

/-- Against an overlong `[true, true, true]` oracle reply, adapting at outer prefix `r = 2`
returns `[false, true, true]`: taking the `2`-bit prefix before translation differs from
truncating after translation (`[false, true]`) and from using `capIn = 3`
(`[false, true, true, true]`). -/
theorem prependFalseMap_adapt_prefix_before_translate :
    ProbOracleComp.runWith tripleOracle
        (ProbOracleComp.lowerWith (WordInterface.net msgPort) 2
          (prependFalseMap.adapt
            (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) []))) () =
      PMF.pure ([false, true, true], ()) ∧
    ([false, true, true] ≠ [false, true] ∧ [false, true, true] ≠ [false, true, true, true]) := by
  refine ⟨?_, by decide, by decide⟩
  simp only [prependFalseMap, WordInterface.PortMap.adapt, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_map, ProbOracleComp.simulate_query, WordInterface.lowerQuery,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, tripleOracle, PMF.pure_map]
  rfl

end LengthChangingAdapterWitness

/-! ### 2. `corruptRouter` branches and certificate witness on `coinStore` -/

section CorruptRouterWitness

/-- Under `corruptRouter {1} (coinStore.toProtocol κ {1})`, environment inputs to corrupted party
`1` return `none` without changing state, adversary-routed inputs to party `1` forward to
`coinStore`, and environment inputs to honest party `0` reach `coinStore`. -/
theorem coinStore_corruptRouter_branches (κ : ℕ) (b : Bool) :
    (corruptRouter ({1} : Finset (Fin 2)) (coinStore.toProtocol κ {1})).handle
        (Sum.inl ((1 : Fin 2), b)) = pure none ∧
    (corruptRouter ({1} : Finset (Fin 2)) (coinStore.toProtocol κ {1})).handle
        (Sum.inr (.inl ((1 : Fin 2), b))) =
      Sum.inl <$> (coinStore.toProtocol κ {1}).handle (Sum.inl ((1 : Fin 2), b)) ∧
    (corruptRouter ({1} : Finset (Fin 2)) (coinStore.toProtocol κ {1})).handle
        (Sum.inl ((0 : Fin 2), b)) =
      (coinStore.toProtocol κ {1}).handle (Sum.inl ((0 : Fin 2), b)) := by
  have h1 : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by decide
  have h0 : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp [corruptRouter, h1]; rfl
  · simp [corruptRouter, h1]
  · simp [corruptRouter, h0]

/-- Concrete routed poll evaluation on `corruptRouter {1} (coinStore.toProtocol κ {1})`: an
adversary-routed poll at corrupted party `1` returns `Sum.inl (some s)` without modifying state. -/
theorem coinStore_corruptRouter_adv_poll_eval (κ : ℕ) (b : Bool) (s : List Bool) :
    ProbOracleComp.runWith emptyWordOracle
        (ProbOracleComp.lowerWith WordInterface.empty 0
          (((corruptRouter ({1} : Finset (Fin 2)) (coinStore.toProtocol κ {1})).handle
            (Sum.inr (.inl ((1 : Fin 2), b)))).run s)) () =
      PMF.pure (((Sum.inl (some s) : RoutedNetR (List Bool) Unit), s), ()) := by
  rw [(coinStore_corruptRouter_branches κ b).2.1]
  let s' : coinStore.State := s
  have hev : ((coinStore.onInput (1 : Fin 2) b).run s').eval =
      PMF.pure ((some s : Option (List Bool)), s') :=
    coinStore_onInput_one_eval b s
  change ProbOracleComp.runWith emptyWordOracle
      (ProbOracleComp.lowerWith WordInterface.empty 0
        (Prod.map Sum.inl id <$>
          ProbOracleComp.sample ((coinStore.onInput (1 : Fin 2) b).run s'))) () = _
  rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_map, ProbOracleComp.simulate_sample,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_sample, hev, PMF.pure_map, PMF.pure_map]
  rfl

/-- Static-corruption routing around `coinStore.toProtocol` preserves `Protocol.IsPPT`, using
`WordPort.computable_partyIndex` to extract the party index from `coinPartyPort`. -/
theorem coinStore_corruptRouter_isPPT :
    Protocol.IsPPT (fun κ C => corruptRouter C (coinStore.toProtocol κ C))
      coinPartyPort (WordPort.sum coinPartyPort unitPort) :=
  coinStore_toProtocol_isPPT.corruptRouter (WordPort.computable_partyIndex coinInputPort)

end CorruptRouterWitness

/-! ### 3. Logging adversary and `liftAdversary` witness -/

section LiftAdversaryWitness

/-- Stateful adversary keeping a unary call counter, forwarding every `List Bool` query to the
network port and incrementing its counter by `1` on each activation. -/
private def logAdv : Adversary 2 (List Bool) (List Bool) (List Bool) (List Bool) :=
  fun _ _ =>
    { State := ℕ
      init := pure 0
      handle := fun q c => do
        let r ← ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) q
        pure (r, c + 1) }

private theorem logAdv_wordHandle_eq (p : PPTParam 2) (w sw : List Bool) :
    wordHandle logAdv (WordInterface.net msgPort) (WordInterface.net msgPort)
        (fun _ _ => unaryCodec) p ((), w) sw =
      (fun r => (r, encUnary (Decoder.unary.decode sw + 1))) <$>
        ProbOracleComp.lowerWith (WordInterface.net msgPort) p.replyBound
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) w) := by
  simp only [wordHandle, logAdv, unaryCodec, StateT.run, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pure]
  rfl

private def logAdvCert :
    PPTCertificate logAdv (WordInterface.net msgPort) (WordInterface.net msgPort) where
  codec _ _ := unaryCodec
  init := by
    change IsPPTOn (encPPTParam 2) encBits (fun _ => pure (encUnary 0))
    exact (ComputableInPolyTime.const (encUnary 0)).isPPTOn
  handle := by
    refine (isOraclePPTOn_forwardAndIncUnary (n := 2)
        (chOut := (WordInterface.net msgPort).Channel) (WordInterface.net msgPort) ()).congr
      fun x State oracle s => ?_
    rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
    rw [logAdv_wordHandle_eq]
    rfl
  normalize := computable_normalize_unary 2
  growth _ _ := 1
  growth_poly := PolyBounded.const 1
  preserve p req s result hr := by
    rcases req with ⟨⟨⟩, w⟩
    rw [logAdv_wordHandle_eq] at hr
    simp only [OracleComp.mem_supportWith_map_iff] at hr
    rcases hr with ⟨_, _, rfl⟩
    let s' : ℕ := s
    have hdec : Decoder.unary.decode (encUnary s') = s' := Decoder.unary.decode_enc s'
    change (encUnary (Decoder.unary.decode (encUnary s') + 1)).length ≤ (encUnary s').length + 1
    rw [hdec]
    simp only [encUnary_apply, List.length_replicate]
    omega

/-- `logAdv` is strict PPT. -/
theorem logAdv_isPPT : logAdv.IsPPT msgPort msgPort :=
  ⟨logAdvCert⟩

/-- Lifting `logAdv` past the party port yields a strict-PPT machine family over
`WordInterface.exec coinPartyPort msgPort`. -/
theorem logAdv_liftAdversary_isPPT :
    Machine.IsPPTFamily (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
      (WordInterface.protocol coinPartyPort msgPort)
      (WordInterface.exec coinPartyPort msgPort) :=
  logAdv_isPPT.liftAdversary

/-- On `liftAdversary (logAdv κ C)`, a party-channel word activation forwards on the left channel
and re-encodes even an off-image state word `[false]` into `Set.range encUnary` (`≠ [false]`). -/
theorem logAdv_liftAdversary_forwards_party_and_normalizes (p : PPTParam 2) (w : List Bool) :
    let cert := logAdvCert.liftAdversary coinPartyPort
    let iIn := WordInterface.protocol coinPartyPort msgPort
    let iOut := WordInterface.exec coinPartyPort msgPort
    let noneOracle : iIn.Channel × List Bool → StateT Unit PMF (List Bool) :=
      fun _ _ => PMF.pure (coinPartyPort.reply none, ())
    (∀ sw : List Bool,
      wordHandle (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
          iIn iOut cert.codec p (.inl (), w) sw =
        (fun r => (coinPartyPort.reply r, encUnary (Decoder.unary.decode sw))) <$>
          ProbOracleComp.lowerWith iIn p.replyBound
            (ProbOracleComp.query
              (spec := protocolSpec 2 Bool (List Bool) (List Bool) (List Bool))
              (.inl (coinPartyPort.queryDecoder.decode w)))) ∧
    (encUnary (Decoder.unary.decode [false]) ≠ [false] ∧
      ProbOracleComp.runWith noneOracle
        (wordHandle (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
          iIn iOut cert.codec ⟨p.secParam, 1, p.corrupted⟩ (.inl (), w) [false]) () =
      PMF.pure ((coinPartyPort.reply none, encUnary (Decoder.unary.decode [false])), ())) := by
  have hfwd : ∀ (q : PPTParam 2) (sw : List Bool),
      wordHandle (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
          (WordInterface.protocol coinPartyPort msgPort)
          (WordInterface.exec coinPartyPort msgPort)
          (logAdvCert.liftAdversary coinPartyPort).codec q (.inl (), w) sw =
        (fun r => (coinPartyPort.reply r, encUnary (Decoder.unary.decode sw))) <$>
          ProbOracleComp.lowerWith (WordInterface.protocol coinPartyPort msgPort) q.replyBound
            (ProbOracleComp.query
              (spec := protocolSpec 2 Bool (List Bool) (List Bool) (List Bool))
              (.inl (coinPartyPort.queryDecoder.decode w))) := by
    intro q sw
    simp only [wordHandle, liftAdversary, Machine.liftRight, PPTCertificate.liftAdversary,
      PPTCertificate.liftRight, logAdvCert, StateT.run, ProbOracleComp.lowerWith]
    rfl
  refine ⟨hfwd p, ?_, ?_⟩
  · intro h
    have hmem : false ∈ ([false] : List Bool) := by simp
    rw [← h, encUnary_apply] at hmem
    simp at hmem
  · have hfwd2 := hfwd ⟨p.secParam, 1, p.corrupted⟩ [false]
    dsimp only at hfwd2
    change ProbOracleComp.runWith _
        (wordHandle (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
          (WordInterface.protocol coinPartyPort msgPort)
          (WordInterface.exec coinPartyPort msgPort)
          (logAdvCert.liftAdversary coinPartyPort).codec ⟨p.secParam, 1, p.corrupted⟩
          (.inl (), w) [false]) () = _
    rw [hfwd2, ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, WordInterface.lowerQuery,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, PMF.pure_map, PMF.pure_map, PMF.pure_map]
    rfl

end LiftAdversaryWitness

end CslibFrontierTests.Crypto.UCPPTWrappers
