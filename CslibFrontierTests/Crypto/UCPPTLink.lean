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

/-! ### 3. Negative witness: `Machine.IsReplyBounded` cannot be dropped -/

section NegativeCompWitness

private def punitCodec : WordCodec PUnit where
  enc := encUnit
  decode := unitDecoder.decode
  decode_enc := unitDecoder.decode_enc

/-- Stateless machine doubling its incoming bitstring `w ↦ w ++ w`. Its replies satisfy `|w ++ w| ≤
2 * |w|` (even bounded linearly in the request), yet it fails `Machine.IsReplyBounded`. -/
private def doubleMachine :
    ℕ → Finset (Fin 2) → Machine OracleSpec.empty (netSpec (List Bool) (List Bool)) :=
  fun _ _ =>
    { State := PUnit
      init := pure PUnit.unit
      handle := fun w _ => pure (w ++ w, PUnit.unit) }

/-- `doubleMachine` is strict PPT (`Machine.IsPPTFamily`). -/
theorem doubleMachine_isPPT :
    Machine.IsPPTFamily doubleMachine WordInterface.empty (WordInterface.net msgPort) := by
  refine ⟨{
    codec := fun _ _ => punitCodec
    init := (ComputableInPolyTime.const (encUnit ())).isPPTOn
    handle := by
      let EIn :=
        encHandlerCall (encPPTParam 2) (encFinite (WordInterface.net msgPort).Channel) encBits
      have hword : ComputableInPolyTime
          (fun x : PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool =>
            x.2.1.2)
          EIn encBits := by
        unfold EIn encHandlerCall; fun_prop
      have hdouble : ComputableInPolyTime
          (fun x : PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool =>
            (x.2.1.2 ++ x.2.1.2, encUnit ()))
          EIn (encPair encBits encBits) :=
        (ComputableInPolyTime.bitsAppend hword hword).prod
          (ComputableInPolyTime.const (encIn := EIn) (encOut := encBits) (encUnit ()))
      refine (hdouble.isOraclePPTOn (Operation := WordInterface.empty.Channel)).congr
        fun x State oracle s => ?_
      rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
      change ProbOracleComp.runWith oracle (pure (w ++ w, encUnit ())) s =
        ProbOracleComp.runWith oracle
          (wordHandle doubleMachine WordInterface.empty (WordInterface.net msgPort)
            (fun _ _ => punitCodec) p ((), w) sw) s
      rw [ProbOracleComp.runWith_pure]
      change PMF.pure ((w ++ w, encUnit ()), s) = ProbOracleComp.runWith oracle
        (ProbOracleComp.lowerWith WordInterface.empty p.replyBound
          (pure (w ++ w, punitCodec.enc PUnit.unit))) s
      rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_pure, ProbOracleComp.runWith_pure]
      rfl
    normalize := ComputableInPolyTime.const (encUnit ())
    growth := fun _ _ => 0
    growth_poly := PolyBounded.const 0
    preserve := fun p req s out hout => by
      cases s
      rcases req with ⟨⟨⟩, w⟩
      change out ∈ OracleComp.support
          (wordHandle doubleMachine WordInterface.empty (WordInterface.net msgPort)
            (fun _ _ => punitCodec) p ((), w) (punitCodec.enc PUnit.unit)) at hout
      simp only [wordHandle, doubleMachine, punitCodec, StateT.run, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure, OracleComp.support] at hout
      subst hout
      simp only [punitCodec]
      omega }⟩

/-- `doubleMachine` is not `Machine.IsReplyBounded` (even though replies are at most `2 * |w|`). -/
theorem doubleMachine_not_isReplyBounded :
    ¬ Machine.IsReplyBounded doubleMachine WordInterface.empty (WordInterface.net msgPort) := by
  rintro ⟨bound, _, hle⟩
  let p : PPTParam 2 := ⟨0, 0, ∅⟩
  let w : List Bool := List.replicate (bound p + 1) true
  have hmem : (w ++ w, PUnit.unit) ∈ OracleComp.support
      (ProbOracleComp.lowerWith WordInterface.empty p.replyBound
        (((doubleMachine p.secParam p.corrupted).handle w).run PUnit.unit)) := by
    simp only [doubleMachine, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_pure,
      OracleComp.support, OracleComp.supportWith_pure]
    rfl
  have hlen := hle p w PUnit.unit (w ++ w, PUnit.unit) hmem
  change (msgPort.reply (w ++ w)).length ≤ bound p at hlen
  simp only [msgPort, encBits_apply, List.length_append, w, List.length_replicate] at hlen
  omega

/-- Stateless outer machine making `κ` sequential queries, feeding each reply as the next
request, and returning the final reply. -/
private def iterQueryMachine :
    ℕ → Finset (Fin 2) →
      Machine (netSpec (List Bool) (List Bool)) (netSpec (List Bool) (List Bool)) :=
  fun κ _ =>
    { State := PUnit
      init := pure PUnit.unit
      handle := fun w _ =>
        (·, PUnit.unit) <$>
          OracleComp.iterate κ
            (fun x => ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x) w }

private theorem lowerWith_iterate_net (limit k : ℕ) (w : List Bool) :
    ProbOracleComp.lowerWith (WordInterface.net msgPort) limit
        (OracleComp.iterate k
          (fun x => ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x) w) =
      OracleComp.iterate k
        (fun x => ProbOracleComp.lowerWith (WordInterface.net msgPort) limit
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x)) w := by
  rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
    OracleComp.interpret_iterate]
  rfl

/-- `iterQueryMachine` is strict PPT (`Machine.IsPPTFamily`). -/
theorem iterQueryMachine_isPPT :
    Machine.IsPPTFamily iterQueryMachine
      (WordInterface.net msgPort) (WordInterface.net msgPort) := by
  let EIn :=
    encHandlerCall (encPPTParam 2) (encFinite (WordInterface.net msgPort).Channel) encBits
  have hcount : ComputableInPolyTime
      (fun x : PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool =>
        x.1.secParam)
      EIn encUnary := by
    unfold EIn encHandlerCall; fun_prop
  have hinit : ComputableInPolyTime
      (fun x : PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool =>
        msgPort.queryDecoder.decode x.2.1.2)
      EIn encBits := by
    refine msgPort.queryDecoder.computableInPolyTime.comp ?_
    unfold EIn encHandlerCall; fun_prop
  have hrc : ComputableInPolyTime
      (fun x : PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool =>
        x.1.replyBound)
      EIn encUnary := by
    unfold EIn encHandlerCall; fun_prop
  have hstep : IsOraclePPTOn (encPair EIn encBits) encBits
      (fun pair : (PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool) ×
          List Bool =>
        ProbOracleComp.lowerWith (WordInterface.net msgPort) pair.1.1.replyBound
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) pair.2)) := by
    have hq := (WordInterface.net msgPort).isOraclePPTOn_lowerWith_decodeQuery
      (input := encPair EIn encBits)
      (ch := fun _ => ())
      (word := fun pair => pair.2)
      (limit := fun pair => pair.1.1.replyBound)
      (ComputableInPolyTime.const ())
      (ComputableInPolyTime.snd EIn encBits)
      (hrc.comp (ComputableInPolyTime.fst EIn encBits))
    refine hq.congr fun pair State oracle s => ?_
    rfl
  have hrb : PolyBounded (fun x : PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) ×
      List Bool => (EIn x).length) (fun x => x.1.replyBound) := by
    simpa only [encUnary_apply, List.length_replicate] using hrc.polyBounded_length
  have hloop : IsOraclePPTOn EIn encBits
      (fun x : PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool =>
        OracleComp.iterate x.1.secParam
          (fun state => ProbOracleComp.lowerWith (WordInterface.net msgPort) x.1.replyBound
            (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) state))
          (msgPort.queryDecoder.decode x.2.1.2)) := by
    refine IsOraclePPTOn.iterateWith_of_bounded_growth hcount hinit hstep hrb
      fun x state next hnext => ?_
    simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, WordInterface.lowerQuery,
      WordInterface.net, msgPort, Decoder.bits, id_eq] at hnext
    rcases OracleComp.mem_supportWith_map_iff.mp hnext with ⟨t, ht, rfl⟩
    rcases OracleComp.mem_supportWith_map_iff.mp ht with ⟨w, _, rfl⟩
    simp only [encBits_apply, id_eq, List.length_take]
    omega
  refine ⟨{
    codec := fun _ _ => punitCodec
    init := (ComputableInPolyTime.const (encUnit ())).isPPTOn
    handle := by
      have hid : ComputableInPolyTime (fun x : List Bool => x) encBits encBits := by fun_prop
      have hpair := hloop.map
        (hid.prod (ComputableInPolyTime.const (encIn := encBits) (encOut := encBits) (encUnit ())))
      refine hpair.congr fun x State oracle s => ?_
      rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
      change ProbOracleComp.runWith oracle ((fun a => (a, encUnit ())) <$>
          OracleComp.iterate p.secParam
            (fun state => ProbOracleComp.lowerWith (WordInterface.net msgPort) p.replyBound
              (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) state))
            (msgPort.queryDecoder.decode w)) s =
        ProbOracleComp.runWith oracle
          (wordHandle iterQueryMachine (WordInterface.net msgPort) (WordInterface.net msgPort)
            (fun _ _ => punitCodec) p ((), w) sw) s
      have hwh : wordHandle iterQueryMachine (WordInterface.net msgPort) (WordInterface.net msgPort)
          (fun _ _ => punitCodec) p ((), w) sw =
          (fun a => (msgPort.reply a, punitCodec.enc PUnit.unit)) <$>
            ProbOracleComp.lowerWith (WordInterface.net msgPort) p.replyBound
              (OracleComp.iterate p.secParam
                (fun x => ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x)
                (msgPort.queryDecoder.decode w)) := by
        simp only [wordHandle, iterQueryMachine, StateT.run, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_map, Functor.map_map]
        rfl
      rw [hwh, lowerWith_iterate_net]
      rfl
    normalize := ComputableInPolyTime.const (encUnit ())
    growth := fun _ _ => 0
    growth_poly := PolyBounded.const 0
    preserve := fun p req s out hout => by
      rcases req with ⟨⟨⟩, w⟩
      cases s
      change out ∈ OracleComp.support
          (wordHandle iterQueryMachine (WordInterface.net msgPort) (WordInterface.net msgPort)
            (fun _ _ => punitCodec) p ((), w) (punitCodec.enc PUnit.unit)) at hout
      simp only [wordHandle, iterQueryMachine, punitCodec, StateT.run,
        ProbOracleComp.lowerWith, ProbOracleComp.simulate_map, OracleComp.support,
        OracleComp.supportWith_map, Set.mem_image] at hout
      rcases hout with ⟨⟨_, w2⟩, _, rfl⟩
      cases w2
      simp only [punitCodec]
      omega }⟩

private theorem queriesSatisfy_iterate_net (limit k : ℕ) (B : ℕ) (w : List Bool)
    (hw : w.length ≤ B) (hlim : limit ≤ B) :
    OracleComp.QueriesSatisfy
      (fun op => Sum.elim (fun _ => True)
        (fun cw : (WordInterface.net msgPort).Channel × List Bool => cw.2.length ≤ B) op)
      (OracleComp.iterate k
        (fun x => ProbOracleComp.lowerWith (WordInterface.net msgPort) limit
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x)) w) := by
  induction k generalizing w with
  | zero => exact OracleComp.QueriesSatisfy.pure w
  | succ k ih =>
    rw [OracleComp.iterate_succ_bind]
    change OracleComp.QueriesSatisfy _
      (ProbOracleComp.query (spec := fun _ : (WordInterface.net msgPort).Channel × List Bool =>
          List Bool) ((), encBits w) >>= fun raw =>
        OracleComp.iterate k
          (fun x => ProbOracleComp.lowerWith (WordInterface.net msgPort) limit
            (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x))
          (Decoder.bits.decode (List.take limit raw)))
    refine OracleComp.QueriesSatisfy.bind
      (OracleComp.QueriesSatisfy.query (q := Sum.inr ((), encBits w)) ?_) fun raw => ?_
    · change w.length ≤ B
      exact hw
    · exact ih (Decoder.bits.decode (List.take limit raw))
        (le_trans (List.length_take_le _ _) hlim)

/-- `iterQueryMachine` is `Machine.IsRequestBounded` with bound `pw.2.length + pw.1.replyBound`. -/
theorem iterQueryMachine_isRequestBounded :
    Machine.IsRequestBounded iterQueryMachine
      (WordInterface.net msgPort) (WordInterface.net msgPort) := by
  have hrb : PolyBounded
      (fun pw : PPTParam 2 × List Bool => (encPair (encPPTParam 2) encBits pw).length)
      (fun pw => pw.2.length + pw.1.replyBound) := by
    have h1 : ComputableInPolyTime
        (fun pw : PPTParam 2 × List Bool => pw.2.length + pw.1.replyBound)
        (encPair (encPPTParam 2) encBits) encUnary := by
      have hlen : ComputableInPolyTime (fun pw : PPTParam 2 × List Bool => pw.2.length)
          (encPair (encPPTParam 2) encBits) encUnary := by
        simpa only [encBits_apply, Function.comp_def] using
          (ComputableInPolyTime.encoding_length encBits).comp
            (ComputableInPolyTime.snd (encPPTParam 2) encBits)
      have hr : ComputableInPolyTime (fun pw : PPTParam 2 × List Bool => pw.1.replyBound)
          (encPair (encPPTParam 2) encBits) encUnary := by
        fun_prop
      exact ComputableInPolyTime.unary_add.comp (hlen.prod hr)
    simpa only [encUnary_apply, List.length_replicate] using h1.polyBounded_length
  refine ⟨fun pw => pw.2.length + pw.1.replyBound, hrb, fun p q s => ?_⟩
  simp only [iterQueryMachine, StateT.run, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_map, OracleComp.queriesSatisfy_map_iff]
  rw [← ProbOracleComp.lowerWith, lowerWith_iterate_net]
  exact queriesSatisfy_iterate_net p.replyBound p.secParam (q.length + p.replyBound) q
    (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- `iterQueryMachine κ C` has per-activation call budget `κ + 1`. -/
theorem iterQueryMachine_isBounded (κ : ℕ) (C : Finset (Fin 2)) :
    (iterQueryMachine κ C).IsBounded (κ + 1) := by
  refine ⟨(OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _), fun q s => ?_⟩
  simp only [iterQueryMachine, StateT.run, OracleComp.isCostBounded_map_iff]
  have hiter : ∀ k w, (OracleComp.iterate k
      (fun x => ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x)
        w).IsQueryBounded k := by
    intro k
    induction k with
    | zero => intro w; exact OracleComp.IsCostBounded.pure w 0
    | succ k ih =>
      intro w
      rw [OracleComp.iterate_succ]
      exact OracleComp.IsCostBounded.bind (ih w)
        (fun a => OracleComp.IsCostBounded.query (q := Sum.inr a))
  exact (hiter κ q).mono (Nat.le_succ κ)

private theorem runFrom_double_iterate (κ k : ℕ) (x : List Bool) :
    (doubleMachine κ ∅).runFrom
        (OracleComp.iterate k
          (fun w => ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) w) x)
        (PUnit.unit : (doubleMachine κ ∅).State) =
      pure (Nat.iterate (fun w => w ++ w) k x, (PUnit.unit : (doubleMachine κ ∅).State)) := by
  dsimp only [doubleMachine]
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [OracleComp.iterate_succ, Machine.runFrom_bind, ih x, pure_bind, Machine.runFrom_query]
    simp only [StateT.run, Function.iterate_succ_apply']

private theorem length_iterate_double (k : ℕ) (x : List Bool) :
    (Nat.iterate (fun w => w ++ w) k x).length = 2 ^ k * x.length := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (x ++ x), List.length_append, pow_succ]
    ring

private theorem exists_poly_lt_two_pow (c d : ℕ) : ∃ κ, c * (κ + 1) ^ d < 2 ^ κ := by
  have hsq : ∀ m : ℕ, (m + 4) ^ 2 ≤ 2 ^ (m + 6) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      have h1 : 2 * m + 9 ≤ (m + 4) ^ 2 := by nlinarith
      have h2 : 2 * m + 9 ≤ 2 ^ (m + 6) := h1.trans ih
      calc
        (m + 1 + 4) ^ 2 = (m + 4) ^ 2 + (2 * m + 9) := by ring
        _ ≤ 2 ^ (m + 6) + 2 ^ (m + 6) := Nat.add_le_add ih h2
        _ = 2 ^ (m + 1 + 6) := by rw [pow_succ]; ring
  let k : ℕ := 2 * d + c + 6
  refine ⟨2 ^ k, ?_⟩
  have hc : c < 2 ^ c := Nat.lt_pow_self (by decide : 1 < 2)
  have hbase : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
    calc
      2 ^ k + 1 ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left hpos _
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hexp : c + (k + 1) * d ≤ 2 ^ k := by
    have hk : c + (k + 1) * d ≤ (2 * d + c + 4) ^ 2 := by
      dsimp only [k]
      nlinarith
    exact hk.trans (hsq (2 * d + c))
  calc
    c * (2 ^ k + 1) ^ d < 2 ^ c * (2 ^ (k + 1)) ^ d :=
      Nat.mul_lt_mul_of_lt_of_le hc (Nat.pow_le_pow_left hbase d)
        (Nat.pow_pos (Nat.pow_pos (by decide : 0 < 2)))
    _ = 2 ^ (c + (k + 1) * d) := by rw [← pow_mul, mul_comm (k + 1) d, ← pow_add]
    _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by decide) hexp

/-- Negative witness: omitting `Machine.IsReplyBounded` makes sequential composition closure
false (`¬ Machine.IsPPTFamily (fun κ C => (iterQueryMachine κ C).comp (doubleMachine κ C))`), even
though `doubleMachine` is PPT (with replies bounded by `2 * |w|`), `iterQueryMachine` is PPT,
request-bounded, and call-bounded (`κ + 1`). Contradiction uses both `cert.init.length_le` and
`cert.handle.length_le`. -/
theorem negative_comp_not_isPPT :
    ¬ Machine.IsPPTFamily (fun κ C => (iterQueryMachine κ C).comp (doubleMachine κ C))
      WordInterface.empty (WordInterface.net msgPort) := by
  rintro ⟨cert⟩
  obtain ⟨c0, d0, hinit⟩ := cert.init.length_le
  obtain ⟨c1, d1, hhandle⟩ := cert.handle.length_le
  have hp : ComputableInPolyTime (fun κ : ℕ => (⟨κ, 0, ∅⟩ : PPTParam 2))
      encUnary (encPPTParam 2) := by
    have hconst : ComputableInPolyTime (fun _ : ℕ => (∅ : Finset (Fin 2)))
        encUnary (encFinite (Finset (Fin 2))) :=
      ComputableInPolyTime.const ∅
    fun_prop
  obtain ⟨cp, dp, hcp⟩ := hp.polyBounded_length.exists_le
  let D : ℕ := max dp (dp * d0)
  let M0 : ℕ := cp + 1
  let Minit : ℕ := c0 * M0 ^ d0
  let Mchan : ℕ := Nat.card (WordInterface.net msgPort).Channel
  let A : ℕ := 2 * M0 + 4 * (Mchan + 2) + Minit + 6
  let Ctot : ℕ := c1 * (A + 1) ^ d1
  obtain ⟨κ, hκ⟩ := exists_poly_lt_two_pow Ctot (D * d1)
  let p : PPTParam 2 := ⟨κ, 0, ∅⟩
  let s0 : ((iterQueryMachine κ ∅).comp (doubleMachine κ ∅)).State := (PUnit.unit, PUnit.unit)
  have hmemInit : (cert.codec κ ∅).enc s0 ∈
      (ProbComp.eval ((cert.codec κ ∅).enc <$>
        ((iterQueryMachine κ ∅).comp (doubleMachine κ ∅)).init)).support := by
    change (cert.codec κ ∅).enc s0 ∈ (ProbComp.eval ((cert.codec κ ∅).enc <$>
      (pure s0 : ProbComp _))).support
    rw [map_pure, ProbComp.eval_pure]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have hlenP : (encPPTParam 2 p).length ≤ cp * (κ + 1) ^ dp := by
    simpa only [encUnary_apply, List.length_replicate] using hcp κ
  have hlenP' : (encPPTParam 2 p).length + 1 ≤ M0 * (κ + 1) ^ D := by
    have hpow : (κ + 1) ^ dp ≤ (κ + 1) ^ D :=
      Nat.pow_le_pow_right (Nat.succ_pos κ) (le_max_left _ _)
    have hpow1 : 1 ≤ (κ + 1) ^ D := Nat.one_le_pow _ _ (Nat.succ_pos κ)
    calc
      (encPPTParam 2 p).length + 1 ≤ cp * (κ + 1) ^ dp + 1 := Nat.add_le_add_right hlenP 1
      _ ≤ cp * (κ + 1) ^ D + (κ + 1) ^ D :=
        Nat.add_le_add (Nat.mul_le_mul_left cp hpow) hpow1
      _ = M0 * (κ + 1) ^ D := by simp [M0, Nat.add_mul]
  have hlenInit : ((cert.codec κ ∅).enc s0).length ≤ Minit * (κ + 1) ^ D := by
    have hi := hinit p ((cert.codec κ ∅).enc s0) hmemInit
    have hpow0 : ((encPPTParam 2 p).length + 1) ^ d0 ≤ (M0 * (κ + 1) ^ dp) ^ d0 := by
      have h1 : (encPPTParam 2 p).length + 1 ≤ M0 * (κ + 1) ^ dp := by
        have hpow1 : 1 ≤ (κ + 1) ^ dp := Nat.one_le_pow _ _ (Nat.succ_pos κ)
        calc
          (encPPTParam 2 p).length + 1 ≤ cp * (κ + 1) ^ dp + 1 := Nat.add_le_add_right hlenP 1
          _ ≤ cp * (κ + 1) ^ dp + (κ + 1) ^ dp := Nat.add_le_add_left hpow1 _
          _ = M0 * (κ + 1) ^ dp := by simp [M0, Nat.add_mul]
      exact Nat.pow_le_pow_left h1 d0
    have hpowD : (κ + 1) ^ (dp * d0) ≤ (κ + 1) ^ D :=
      Nat.pow_le_pow_right (Nat.succ_pos κ) (le_max_right _ _)
    calc
      ((cert.codec κ ∅).enc s0).length
        ≤ c0 * ((encPPTParam 2 p).length + 1) ^ d0 := hi
      _ ≤ c0 * (M0 * (κ + 1) ^ dp) ^ d0 := Nat.mul_le_mul_left c0 hpow0
      _ = Minit * (κ + 1) ^ (dp * d0) := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ Minit * (κ + 1) ^ D := Nat.mul_le_mul_left Minit hpowD
  have hcompHandle :
      ((iterQueryMachine κ ∅).comp (doubleMachine κ ∅)).handle [true] s0 =
        pure (Nat.iterate (fun w => w ++ w) κ [true], s0) := by
    have hstep :
        ((iterQueryMachine κ ∅).comp (doubleMachine κ ∅)).handle [true] s0 =
          Equiv.prodAssoc _ _ _ <$>
            (doubleMachine κ ∅).runFrom
              ((·, PUnit.unit) <$> OracleComp.iterate κ
                (fun x => ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x)
                [true])
              PUnit.unit := rfl
    have hrun := runFrom_double_iterate κ κ [true]
    dsimp only [doubleMachine] at hstep hrun ⊢
    rw [hstep, Machine.runFrom_map, hrun]
    simp only [map_pure]
    rfl
  let ch0 : (WordInterface.net msgPort).Channel := ()
  let x : PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool :=
    (p, (ch0, [true]), (cert.codec κ ∅).enc s0)
  have hmemHandle : ((Nat.iterate (fun w => w ++ w) κ [true], (cert.codec κ ∅).enc s0), ()) ∈
      (ProbOracleComp.runWith (emptyWordOracle :
          WordInterface.empty.Channel × List Bool → StateT Unit PMF (List Bool))
        (wordHandle (fun κ C => (iterQueryMachine κ C).comp (doubleMachine κ C))
          WordInterface.empty (WordInterface.net msgPort) cert.codec x.1 x.2.1 x.2.2)
        ()).support := by
    change _ ∈ (ProbOracleComp.runWith emptyWordOracle
      (wordHandle (fun κ C => (iterQueryMachine κ C).comp (doubleMachine κ C))
        WordInterface.empty (WordInterface.net msgPort) cert.codec
        p (ch0, [true]) ((cert.codec κ ∅).enc s0)) ()).support
    dsimp only [wordHandle, WordInterface.net, WordInterface.decodeQuery, WordInterface.reply,
      msgPort, Decoder.bits, id_eq, StateT.run, p]
    rw [(cert.codec κ ∅).decode_enc, hcompHandle, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_pure, map_pure, ProbOracleComp.runWith_pure]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have hbound := hhandle x Unit emptyWordOracle () ()
    (Nat.iterate (fun w => w ++ w) κ [true], (cert.codec κ ∅).enc s0) hmemHandle
  have h2pow : 2 ^ κ ≤
      (encPair encBits encBits
        (Nat.iterate (fun w => w ++ w) κ [true], (cert.codec κ ∅).enc s0)).length := by
    have hlen2 : (Nat.iterate (fun w => w ++ w) κ [true]).length = 2 ^ κ := by
      simpa using length_iterate_double κ [true]
    simp only [length_encPair, encBits_apply, hlen2]
    omega
  have hxlen : (encHandlerCall (encPPTParam 2) (encFinite (WordInterface.net msgPort).Channel)
      encBits x).length + 1 ≤ A * (κ + 1) ^ D := by
    have hch : (encFinite (WordInterface.net msgPort).Channel ch0).length ≤ Mchan :=
      (length_encFinite_lt _).le
    have hpowD : 1 ≤ (κ + 1) ^ D := Nat.one_le_pow _ _ (Nat.succ_pos κ)
    simp only [encHandlerCall, length_encPair, encBits_apply, x]
    have h1 : ([true] : List Bool).length = 1 := rfl
    have hsum : 2 * (encPPTParam 2 p).length + 1 +
        (2 * (2 * (encFinite (WordInterface.net msgPort).Channel ch0).length + 1 +
          ([true] : List Bool).length) + 1 + ((cert.codec κ ∅).enc s0).length) + 1 ≤
        2 * (M0 * (κ + 1) ^ D) + (4 * (Mchan + 2) + Minit * (κ + 1) ^ D + 6) := by
      omega
    have hstep : 2 * (M0 * (κ + 1) ^ D) + (4 * (Mchan + 2) + Minit * (κ + 1) ^ D + 6) ≤
        A * (κ + 1) ^ D := by
      have hm : 4 * (Mchan + 2) + 6 ≤ (4 * (Mchan + 2) + 6) * (κ + 1) ^ D :=
        Nat.le_mul_of_pos_right _ hpowD
      calc
        2 * (M0 * (κ + 1) ^ D) + (4 * (Mchan + 2) + Minit * (κ + 1) ^ D + 6)
          ≤ 2 * M0 * (κ + 1) ^ D + (4 * (Mchan + 2) + Minit + 6) * (κ + 1) ^ D := by nlinarith
        _ = A * (κ + 1) ^ D := by simp only [A]; ring
    exact hsum.trans hstep
  have hfinal : 2 ^ κ ≤ Ctot * (κ + 1) ^ (D * d1) := by
    have hpowD1 : ((encHandlerCall (encPPTParam 2)
        (encFinite (WordInterface.net msgPort).Channel)
        encBits x).length + 1) ^ d1 ≤ (A * (κ + 1) ^ D) ^ d1 :=
      Nat.pow_le_pow_left hxlen d1
    have hA1 : A * (κ + 1) ^ D ≤ (A + 1) * (κ + 1) ^ D :=
      Nat.mul_le_mul_right _ (Nat.le_succ A)
    calc
      2 ^ κ ≤ c1 * ((encHandlerCall (encPPTParam 2)
          (encFinite (WordInterface.net msgPort).Channel) encBits x).length + 1) ^ d1 :=
        h2pow.trans hbound
      _ ≤ c1 * (A * (κ + 1) ^ D) ^ d1 := Nat.mul_le_mul_left c1 hpowD1
      _ ≤ c1 * ((A + 1) * (κ + 1) ^ D) ^ d1 :=
        Nat.mul_le_mul_left c1 (Nat.pow_le_pow_left hA1 d1)
      _ = Ctot * (κ + 1) ^ (D * d1) := by rw [mul_pow, ← pow_mul, mul_assoc]
  omega

end NegativeCompWitness

end CslibFrontierTests.Crypto.UCPPTLink
