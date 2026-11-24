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
import CslibFrontier.Crypto.Protocols.UC.PPT
import CslibFrontier.Crypto.Protocols.UC.PPT.Link
import CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontierTests.Crypto.UCPPT

/-!
# Tests for `UC.PPT.Link`

Non-degenerate witnesses for `CslibFrontier.Crypto.Protocols.UC.PPT.Link`:

1. `Machine.IsReplyBounded` admits unbounded growing state and coin-dependent replies
   (`windowProtocol`, returning the `κ`-bit window of a growing coin-masked list; also lifted
   through `Machine.IsReplyBounded.routeCorrupt`), while the certified full-state protocol
   `coinStore.toProtocol` is not reply-bounded (`coinStore_not_isReplyBounded`).
2. `Environment.IsPPT.absorbAdversary` certified for a stateful reply-growing adversary
   `tagLogAdv` and an interactive two-party environment `linkEnv`, together with an explicit
   enlarged-cap witness showing that running `wordRunWith` without enlarging the environment's
   reply bound truncates `tagLogAdv`'s reply and changes the distribution.
3. Negative witness showing that the `Machine.IsReplyBounded` premise cannot be dropped:
   a stateless doubling machine `doubleMachine` is strict PPT (`Machine.IsPPTFamily`) with replies
   bounded by `2 * w.length` (so even a request-dependent reply bound fails), and a `κ`-round
   iterating machine `iterQueryMachine` is strict PPT, request-bounded (`Machine.IsRequestBounded`),
   and call-bounded (`IsBounded (κ + 1)`), yet their sequential composition
   `fun κ C => (iterQueryMachine κ C).comp (doubleMachine κ C)` has no `Machine.IsPPTFamily`
   certificate (using both `cert.init.length_le` and `cert.handle.length_le`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPPTLink

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.UCPPT

private def msgPort : WordPort (List Bool) (List Bool) :=
  ⟨encBits, Decoder.bits, encBits, Decoder.bits⟩

private def unaryCodec : WordCodec ℕ where
  enc := encUnary
  decode := Decoder.unary.decode
  decode_enc := Decoder.unary.decode_enc

/-! ### 1. `IsReplyBounded` with growing state and `¬ IsReplyBounded` for `coinStore` -/

section ReplyBoundWitnesses

/-- Two-party protocol with real coins and unbounded growing state: party `0` appends a
coin-masked bit to the stored list; party `1` polls and receives the `κ`-bit prefix of the list;
the network backdoor is a no-op. -/
private noncomputable def windowProtocol : Protocol 2 Bool (List Bool) Unit Unit := fun κ _ =>
  { State := List Bool
    init := pure []
    handle := fun
      | Sum.inl (i, b), s =>
        if i = 0 then do
          let c ← ProbOracleComp.sample (ProbComp.uniform Bool)
          pure (none, (b ^^ c) :: s)
        else
          pure (some (List.take κ s), s)
      | Sum.inr (), s => pure ((), s) }

/-- On a state of length `2 * κ` (`κ ≥ 1`), polling `windowProtocol` returns a list of length `κ`,
strictly shorter than the state. -/
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
  have hmin : min κ (2 * κ) = κ := by omega
  rw [hmin]

/-- `windowProtocol` satisfies `Machine.IsReplyBounded` with bound `p.secParam + 1`, despite
unbounded state growth and coin-dependent state contents. -/
theorem windowProtocol_isReplyBounded :
    Machine.IsReplyBounded windowProtocol WordInterface.empty
      (WordInterface.protocol coinPartyPort unitPort) := by
  have hsec : PolyBounded (fun p : PPTParam 2 => (encPPTParam 2 p).length)
      (fun p : PPTParam 2 => p.secParam) :=
    ((by fun_prop : ComputableInPolyTime (fun p : PPTParam 2 => p.secParam)
      (encPPTParam 2) encUnary).polyBounded_length).mono fun p => by
      simp [encUnary_apply]
  refine ⟨fun p => p.secParam + 1, hsec.add (PolyBounded.const 1), fun p q s x hx => ?_⟩
  let s' : List Bool := s
  cases q with
  | inl ib =>
    rcases ib with ⟨i, b⟩
    by_cases hi : i = 0
    · let x' : Option (List Bool) × List Bool := x
      have hx0 : x' ∈ OracleComp.supportWith (fun _ => Set.univ)
          ((ProbOracleComp.sample (ProbComp.uniform Bool) >>= fun c =>
            pure ((none : Option (List Bool)), (b ^^ c) :: s')) :
              WordOracleComp WordInterface.empty.Channel (Option (List Bool) × List Bool)) := by
        simp only [windowProtocol, StateT.run, hi, ↓reduceIte, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample,
          ProbOracleComp.simulate_pure, OracleComp.support] at hx
        exact hx
      rw [OracleComp.mem_supportWith_bind_iff] at hx0
      rcases hx0 with ⟨c, _, hc⟩
      have hx' := OracleComp.eq_of_mem_supportWith_pure hc
      have h1 : x'.1 = none := congrArg Prod.fst hx'
      change (coinPartyPort.reply x'.1).length ≤ p.secParam + 1
      rw [h1]
      simp [coinPartyPort, WordPort.party, encOption_none]
    · simp only [windowProtocol, StateT.run, hi, ↓reduceIte, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure, OracleComp.support] at hx
      have hx' := OracleComp.eq_of_mem_supportWith_pure hx
      subst hx'
      change (coinPartyPort.reply (some (List.take p.secParam s'))).length ≤ p.secParam + 1
      simp only [coinPartyPort, WordPort.party, coinInputPort, encOption_some, encBits_apply,
        List.length_cons]
      have htake : (List.take p.secParam s').length ≤ p.secParam := List.length_take_le _ _
      omega
  | inr u =>
    cases u
    simp only [windowProtocol, StateT.run, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_pure, OracleComp.support] at hx
    have hx' := OracleComp.eq_of_mem_supportWith_pure hx
    subst hx'
    change ([] : List Bool).length ≤ p.secParam + 1
    simp

/-- Transfer of `windowProtocol_isReplyBounded` through static-corruption routing. -/
theorem windowProtocol_corruptRouter_isReplyBounded :
    Machine.IsReplyBounded (fun κ C => corruptRouter C (windowProtocol κ C)) WordInterface.empty
      (WordInterface.protocol coinPartyPort (WordPort.sum coinPartyPort unitPort)) :=
  windowProtocol_isReplyBounded.routeCorrupt

/-- The certified full-state protocol `coinStore.toProtocol` is not `Machine.IsReplyBounded`:
its party-`1` poll reply grows linearly with the arbitrary state word. -/
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
    List.length_cons, s, List.length_replicate] at hlen
  omega

end ReplyBoundWitnesses

/-! ### 2. `absorbAdversary` witness and enlarged-cap truncation contrast -/

section AbsorbAdversaryWitness

/-- Stateful reply-growing adversary keeping a unary call counter, forwarding every query to the
network port, prepending `true` to the reply (growing its length by `1`), and incrementing the
counter. -/
private def tagLogAdv : Adversary 2 (List Bool) (List Bool) (List Bool) (List Bool) :=
  fun _ _ =>
    { State := ℕ
      init := pure 0
      handle := fun q c => do
        let r ← ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) q
        pure (true :: r, c + 1) }

private theorem tagLogAdv_wordHandle_eq (p : PPTParam 2) (w sw : List Bool) :
    wordHandle tagLogAdv (WordInterface.net msgPort) (WordInterface.net msgPort)
        (fun _ _ => unaryCodec) p ((), w) sw =
      (fun r => (true :: r, encUnary (Decoder.unary.decode sw + 1))) <$>
        ProbOracleComp.lowerWith (WordInterface.net msgPort) p.replyBound
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) w) := by
  simp only [wordHandle, tagLogAdv, unaryCodec, StateT.run, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pure]
  rfl

private def tagLogAdvCert :
    PPTCertificate tagLogAdv (WordInterface.net msgPort) (WordInterface.net msgPort) where
  codec _ _ := unaryCodec
  init := by
    change IsPPTOn (encPPTParam 2) encBits (fun _ => pure (encUnary 0))
    exact (ComputableInPolyTime.const (encUnary 0)).isPPTOn
  handle := by
    let EIn := encHandlerCall (encPPTParam 2) (encFinite (WordInterface.net msgPort).Channel)
      encBits
    let iN := WordInterface.net msgPort
    have hq : IsOraclePPTOn EIn encBits
        (fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool =>
          iN.reply (iN.decodeQuery x.2.1.1 x.2.1.2) <$>
            ProbOracleComp.lowerWith iN x.1.replyBound
              (ProbOracleComp.query (iN.decodeQuery x.2.1.1 x.2.1.2))) := by
      refine iN.isOraclePPTOn_lowerWith_decodeQuery
        (ch := fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool => x.2.1.1)
        (word := fun x => x.2.1.2) (limit := fun x => x.1.replyBound) ?_ ?_ ?_ <;>
        (unfold EIn encHandlerCall; fun_prop)
    have hsucc : ComputableInPolyTime
        (fun pair : (PPTParam 2 × (iN.Channel × List Bool) × List Bool) × List Bool =>
          (true :: pair.2, encUnary (Decoder.unary.decode pair.1.2.2 + 1)))
        (encPair EIn encBits) (encPair encBits encBits) := by
      have hrep : ComputableInPolyTime
          (fun pair : (PPTParam 2 × (iN.Channel × List Bool) × List Bool) × List Bool =>
            true :: pair.2)
          (encPair EIn encBits) encBits :=
        ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
          (ComputableInPolyTime.snd EIn encBits)
      have hsw : ComputableInPolyTime
          (fun pair : (PPTParam 2 × (iN.Channel × List Bool) × List Bool) × List Bool =>
            Decoder.unary.decode pair.1.2.2)
          (encPair EIn encBits) encUnary := by
        refine Decoder.unary.computableInPolyTime.comp ?_
        unfold EIn encHandlerCall; fun_prop
      have hinc := (ComputableInPolyTime.of_eq (encIn := encUnary) (encOut := encBits)
        (fun _ => rfl)).comp
        (ComputableInPolyTime.unary_add.comp (hsw.prod (ComputableInPolyTime.const 1)))
      exact hrep.prod hinc
    refine (hq.keep_input.map hsucc).congr fun x State oracle s => ?_
    rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
    rw [tagLogAdv_wordHandle_eq]
    rfl
  normalize :=
    (ComputableInPolyTime.of_eq (encIn := encUnary) (encOut := encBits) (fun _ => rfl)).comp
      (Decoder.unary.computableInPolyTime.comp (ComputableInPolyTime.snd _ _))
  growth _ _ := 1
  growth_poly := PolyBounded.const 1
  preserve p req s' out hout := by
    rcases req with ⟨⟨⟩, w⟩
    rw [tagLogAdv_wordHandle_eq] at hout
    simp only [OracleComp.mem_supportWith_map_iff] at hout
    rcases hout with ⟨_, _, rfl⟩
    let s₀ : ℕ := s'
    have hdec : Decoder.unary.decode (encUnary s₀) = s₀ := Decoder.unary.decode_enc s₀
    change (encUnary (Decoder.unary.decode (encUnary s₀) + 1)).length ≤ (encUnary s₀).length + 1
    rw [hdec]
    simp only [encUnary_apply, List.length_replicate]
    omega

/-- `tagLogAdv` is strict PPT (`Adversary.IsPPT`). -/
theorem tagLogAdv_isPPT : tagLogAdv.IsPPT msgPort msgPort :=
  ⟨tagLogAdvCert⟩

/-- `tagLogAdv` is `Machine.IsReplyBounded` with bound `p.replyBound + 1`. -/
theorem tagLogAdv_isReplyBounded :
    Machine.IsReplyBounded tagLogAdv (WordInterface.net msgPort) (WordInterface.net msgPort) := by
  have hrb : PolyBounded (fun p : PPTParam 2 => (encPPTParam 2 p).length)
      (fun p : PPTParam 2 => p.replyBound) := by
    have hc : ComputableInPolyTime (fun p : PPTParam 2 => p.replyBound)
        (encPPTParam 2) encUnary := by
      fun_prop
    simpa only [encUnary_apply, List.length_replicate] using hc.polyBounded_length
  refine ⟨fun p => p.replyBound + 1, hrb.add (PolyBounded.const 1), fun p q s x hx => ?_⟩
  simp only [tagLogAdv, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery,
    WordInterface.net] at hx
  obtain ⟨r, hr, hx'⟩ := OracleComp.mem_supportWith_bind_iff.mp hx
  obtain ⟨t, ht, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hr
  obtain ⟨w, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp ht
  obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx'
  change (msgPort.reply (true :: msgPort.replyDecoder.decode (List.take p.replyBound w))).length ≤
    p.replyBound + 1
  simp only [msgPort, Decoder.bits, encBits_apply, id_eq, List.length_cons, List.length_take]
  omega

/-- `tagLogAdv` is `Machine.IsRequestBounded` with bound `pw.2.length`. -/
theorem tagLogAdv_isRequestBounded :
    Machine.IsRequestBounded tagLogAdv (WordInterface.net msgPort) (WordInterface.net msgPort) := by
  have hlen : PolyBounded
      (fun pw : PPTParam 2 × List Bool => (encPair (encPPTParam 2) encBits pw).length)
      (fun pw => pw.2.length) :=
    PolyBounded.self.mono fun pw => by
      simp only [length_encPair, encBits_apply]
      omega
  refine ⟨fun pw => pw.2.length, hlen, fun p q s => ?_⟩
  simp only [tagLogAdv, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery,
    WordInterface.net]
  refine OracleComp.QueriesSatisfy.bind ?_ (fun _ => OracleComp.QueriesSatisfy.pure _)
  rw [OracleComp.queriesSatisfy_map_iff, OracleComp.queriesSatisfy_map_iff]
  exact OracleComp.QueriesSatisfy.query (le_refl _)

/-- Interactive two-party environment making two party-`0` writes, one adversary query `[true]`,
and one party-`1` poll, returning `decide (1 < advReply.length)`. -/
private def linkEnv : Environment 2 Bool (List Bool) (List Bool) (List Bool) :=
  fun _ _ => do
    let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), true))
    let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), false))
    let advReply ← ProbOracleComp.query (Sum.inr [true])
    let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), false))
    return decide (1 < advReply.length)

private noncomputable def linkExec :=
  WordInterface.exec coinPartyPort msgPort

private noncomputable def linkConstQuery (q : (Fin 2 × Bool) ⊕ List Bool) (e : EnvParam) :
    WordOracleComp linkExec.Channel (List Bool) :=
  linkExec.reply q <$>
    ProbOracleComp.lowerWith linkExec e.replyBound (ProbOracleComp.query q)

private theorem isOraclePPTOn_linkConstQuery (q : (Fin 2 × Bool) ⊕ List Bool) :
    IsOraclePPTOn encEnvParam encBits (linkConstQuery q) :=
  linkExec.isOraclePPTOn_lowerWith_query
    (query := fun _ : EnvParam => q) (limit := fun e => e.replyBound)
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) (by fun_prop)

/-- `linkEnv` is uniform strict oracle PPT (`Environment.IsPPT`). -/
theorem linkEnv_isPPT : linkEnv.IsPPT coinPartyPort msgPort := by
  let q1 := linkConstQuery (Sum.inl ((0 : Fin 2), true))
  let q2 : EnvParam → List Bool → WordOracleComp linkExec.Channel (List Bool) :=
    fun e _ => linkConstQuery (Sum.inl ((0 : Fin 2), false)) e
  let q3 : EnvParam → List Bool → WordOracleComp linkExec.Channel (List Bool) :=
    fun e _ => linkConstQuery (Sum.inr [true]) e
  let q4 : EnvParam → List Bool → WordOracleComp linkExec.Channel (List Bool) :=
    fun e _ => linkConstQuery (Sum.inl ((1 : Fin 2), false)) e
  have hq1 : IsOraclePPTOn encEnvParam encBits q1 := isOraclePPTOn_linkConstQuery _
  have hq2 : IsOraclePPTOn (encPair encEnvParam encBits) encBits (fun x => q2 x.1 x.2) :=
    (isOraclePPTOn_linkConstQuery _).preprocess (ComputableInPolyTime.fst encEnvParam encBits)
  have hq3 : IsOraclePPTOn (encPair encEnvParam encBits) encBits (fun x => q3 x.1 x.2) :=
    (isOraclePPTOn_linkConstQuery _).preprocess (ComputableInPolyTime.fst encEnvParam encBits)
  have hq4 : IsOraclePPTOn (encPair encEnvParam encBits) encBits (fun x => q4 x.1 x.2) :=
    (isOraclePPTOn_linkConstQuery _).preprocess (ComputableInPolyTime.fst encEnvParam encBits)
  have h12 : IsOraclePPTOn encEnvParam encBits (fun e => q1 e >>= q2 e) :=
    hq1.bind_with (second := q2) hq2
  have h123 : IsOraclePPTOn encEnvParam encBits (fun e => (q1 e >>= q2 e) >>= q3 e) :=
    h12.bind_with (second := q3) hq3
  have h1234 : IsOraclePPTOn encEnvParam encBits
      (fun e => ((q1 e >>= q2 e) >>= q3 e) >>= fun r3 => (fun _ => r3) <$> q4 e r3) := by
    let q4' : EnvParam → List Bool → WordOracleComp linkExec.Channel (List Bool) :=
      fun e r3 => (fun _ => r3) <$> q4 e r3
    have hq4' : IsOraclePPTOn (encPair encEnvParam encBits) encBits (fun x => q4' x.1 x.2) :=
      hq4.map_with (f := fun x _ => x.2)
        ((ComputableInPolyTime.snd encEnvParam encBits).comp (ComputableInPolyTime.fst _ _))
    exact h123.bind_with (second := q4') hq4'
  have hpost : ComputableInPolyTime
      (fun p : EnvParam × List Bool => decide (1 < (msgPort.replyDecoder.decode p.2).length))
      (encPair encEnvParam encBits) encBool := by
    have hdec : ComputableInPolyTime
        (fun p : EnvParam × List Bool => msgPort.replyDecoder.decode p.2)
        (encPair encEnvParam encBits) encBits :=
      msgPort.replyDecoder.computableInPolyTime.comp
        (ComputableInPolyTime.snd encEnvParam encBits)
    have hlen : ComputableInPolyTime
        (fun p : EnvParam × List Bool => (msgPort.replyDecoder.decode p.2).length)
        (encPair encEnvParam encBits) encUnary := by
      simpa only [encBits_apply, Function.comp_def] using
        (ComputableInPolyTime.encoding_length encBits).comp hdec
    have hdec1 : ComputableInPolyTime (fun k : ℕ => decide (1 < k)) encUnary encBool := by
      fun_prop
    simpa only [Function.comp_def] using hdec1.comp hlen
  refine (h1234.keep_input.map hpost).congr fun e State oracle s => ?_
  refine congrArg (fun p => ProbOracleComp.runWith oracle p s) ?_
  simp only [linkEnv, linkExec, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery,
    WordInterface.exec, WordInterface.sum, WordInterface.net, Functor.map_map]
  rfl

/-- Absorbing the reply-growing `tagLogAdv` into `linkEnv` preserves `Environment.IsPPT`. -/
theorem linkEnv_absorbAdversary_isPPT :
    (absorbAdversary ({1} : Finset (Fin 2)) tagLogAdv linkEnv).IsPPT coinPartyPort msgPort :=
  linkEnv_isPPT.absorbAdversary tagLogAdv_isPPT tagLogAdv_isReplyBounded {1}

private noncomputable def oneBitOracle :
    (WordInterface.net msgPort).Channel × List Bool → StateT Unit PMF (List Bool)
  | _, s => PMF.pure ([false], s)

private noncomputable def tagLogAdvWordOracle :
    (WordInterface.net msgPort).Channel × List Bool → StateT (ℕ × Unit) PMF (List Bool)
  | cw, st =>
    (fun x => (msgPort.reply x.1.1, (x.1.2, x.2))) <$>
      ProbOracleComp.runWith oneBitOracle
        (ProbOracleComp.lowerWith (WordInterface.net msgPort) 1
          (((tagLogAdv 0 ∅).handle (msgPort.queryDecoder.decode cw.2)).run st.1)) ()

private theorem tagLogAdvWordOracle_true_zero :
    tagLogAdvWordOracle ((), [true]) (0, ()) = PMF.pure ([true, false], (1, ())) := by
  change (fun x => (msgPort.reply x.1.1, (x.1.2, x.2))) <$>
      ProbOracleComp.runWith oneBitOracle
        (ProbOracleComp.lowerWith (WordInterface.net msgPort) 1
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) [true] >>= fun r =>
            pure (true :: r, (0 : ℕ) + 1))) () =
      PMF.pure ([true, false], (1, ()))
  rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query,
    WordInterface.lowerQuery, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
  have h1bit : oneBitOracle ((WordInterface.net msgPort).channel [true],
      (WordInterface.net msgPort).request [true]) () = PMF.pure ([false], ()) := rfl
  rw [h1bit]
  simp only [ProbOracleComp.simulate_pure, PMF.monad_map_eq_map, PMF.pure_map, PMF.pure_bind,
    Prod.map_apply]
  rw [ProbOracleComp.runWith_pure, PMF.pure_map]
  rfl

/-- Enlarged-cap witness for `tagLogAdv`: when `p.replyBound = 1` and the network oracle returns
`[false]` (1 bit), `tagLogAdv` outputs `[true, false]` (2 bits > `p.replyBound`). Lowering the
caller's query at `p.replyBound = 1` truncates the reply to `[true]`, whereas lowering at enlarged
cap `L = 2 > p.replyBound` delivers `[true, false]` untouched. -/
theorem tagLogAdv_enlarged_cap_prevents_truncation :
    ProbOracleComp.runWith tagLogAdvWordOracle
        (ProbOracleComp.lowerWith (WordInterface.net msgPort) 1
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) [true])) (0, ()) ≠
      ProbOracleComp.runWith tagLogAdvWordOracle
        (ProbOracleComp.lowerWith (WordInterface.net msgPort) 2
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) [true])) (0, ()) := by
  intro h
  have h1 : ProbOracleComp.runWith tagLogAdvWordOracle
      (ProbOracleComp.lowerWith (WordInterface.net msgPort) 1
        (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) [true])) (0, ()) =
      PMF.pure ([true], (1, ())) := by
    rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, WordInterface.lowerQuery,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
    have hq : tagLogAdvWordOracle ((WordInterface.net msgPort).channel [true],
        (WordInterface.net msgPort).request [true]) (0, ()) =
        PMF.pure ([true, false], (1, ())) := tagLogAdvWordOracle_true_zero
    rw [hq, PMF.pure_map, PMF.pure_map]
    rfl
  have h2 : ProbOracleComp.runWith tagLogAdvWordOracle
      (ProbOracleComp.lowerWith (WordInterface.net msgPort) 2
        (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) [true])) (0, ()) =
      PMF.pure ([true, false], (1, ())) := by
    rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, WordInterface.lowerQuery,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
    have hq : tagLogAdvWordOracle ((WordInterface.net msgPort).channel [true],
        (WordInterface.net msgPort).request [true]) (0, ()) =
        PMF.pure ([true, false], (1, ())) := tagLogAdvWordOracle_true_zero
    rw [hq, PMF.pure_map, PMF.pure_map]
    rfl
  have h' := congrArg (fun d => d ([true], (1, ()))) h
  rw [h1, h2] at h'
  simp [PMF.pure_apply] at h'

end AbsorbAdversaryWitness

end CslibFrontierTests.Crypto.UCPPTLink
