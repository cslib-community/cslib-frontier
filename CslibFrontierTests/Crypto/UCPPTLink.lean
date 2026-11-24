/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
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

1. `Machine.IsReplyBounded` admits unbounded coin-masked growing state (`windowProtocol`,
   returning a `κ`-bit prefix, lifted via `Machine.IsReplyBounded.routeCorrupt`), while
   `coinStore.toProtocol` fails `Machine.IsReplyBounded` (`coinStore_not_isReplyBounded`).
2. `Environment.IsPPT.link`, `Machine.IsReplyBounded.liftRight`, and `Machine.IsRequestBounded`
   for a reply-growing adversary `tagAdv` linked with `advPollEnv`, plus an observable witness
   (`tagAdv_enlarged_cap_prevents_truncation`) that un-enlarged truncation drops a bit.
3. Negative witness (`negative_comp_not_isPPT`) showing `Machine.IsReplyBounded` cannot be
   dropped: `doubleMachine` is PPT with `2 * w.length` replies, and `iterQueryMachine` is PPT,
   request-bounded, and `IsBounded (κ + 1)`, yet their sequential composition is not PPT.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPPTLink

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.UCPPT

private def msgPort : WordPort (List Bool) (List Bool) :=
  ⟨encBits, Decoder.bits, encBits, Decoder.bits⟩

private def punitCodec : WordCodec PUnit :=
  ⟨encUnit, unitDecoder.decode, unitDecoder.decode_enc⟩

/-! ### 1. `IsReplyBounded` with growing state and `¬ IsReplyBounded` for `coinStore` -/

section ReplyBoundWitnesses

/-- Two-party protocol with coin-masked growing state: party `0` appends `b ^^ c`, party `1`
polls the `κ`-bit prefix, and the backdoor is a no-op. -/
private noncomputable def windowProtocol : Protocol 2 Bool (List Bool) Unit Unit := fun κ _ =>
  { State := List Bool
    init := pure []
    handle := fun
      | Sum.inl (i, b), s =>
        if i = 0 then do
          let c ← ProbOracleComp.sample (ProbComp.uniform Bool)
          pure (none, (b ^^ c) :: s)
        else pure (some (List.take κ s), s)
      | Sum.inr (), s => pure ((), s) }

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
theorem windowProtocol_isReplyBounded :
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

/-! ### 2. Linking witness and enlarged-cap truncation contrast -/

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
  codec _ _ := punitCodec
  init := (ComputableInPolyTime.const (encUnit ())).isPPTOn
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
    have hstep : ComputableInPolyTime
        (fun w : List Bool => (true :: w, encUnit ())) encBits (encPair encBits encBits) :=
      (ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
        (by fun_prop : ComputableInPolyTime id encBits encBits)).prod
        (ComputableInPolyTime.const (encUnit ()))
    refine (hq.map hstep).congr fun x State oracle s => ?_
    rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
    simp only [wordHandle, tagAdv, StateT.run, ProbOracleComp.lowerWith, Functor.map_map]; rfl
  normalize := ComputableInPolyTime.const (encUnit ())
  growth _ _ := 0
  growth_poly := PolyBounded.const 0
  preserve _ _ s out hout := by
    cases s
    simp only [wordHandle, tagAdv, StateT.run, ProbOracleComp.lowerWith,
      OracleComp.support, OracleComp.supportWith_map, Set.mem_image] at hout
    rcases hout with ⟨⟨_, ⟨⟩⟩, _, rfl⟩; exact le_rfl

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

/-- `tagAdv` is `Machine.IsRequestBounded` with bound `pw.2.length`. -/
theorem tagAdv_isRequestBounded :
    Machine.IsRequestBounded tagAdv (WordInterface.net msgPort) (WordInterface.net msgPort) := by
  have hlen : PolyBounded
      (fun pw : PPTParam 2 × List Bool => (encPair (encPPTParam 2) encBits pw).length)
      (fun pw => pw.2.length) :=
    PolyBounded.self.mono fun pw => by simp only [length_encPair, encBits_apply]; omega
  refine ⟨fun pw => pw.2.length, hlen, fun p q s => ?_⟩
  simp only [tagAdv, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map,
    ProbOracleComp.simulate_query, WordInterface.lowerQuery, WordInterface.net,
    OracleComp.queriesSatisfy_map_iff]
  exact OracleComp.QueriesSatisfy.query (le_refl _)

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

/-- Enlarged-cap witness: against a 1-bit oracle (`[false]`), lowering `tagAdv` at `replyBound = 1`
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

/-! ### 3. Negative witness: `Machine.IsReplyBounded` cannot be dropped -/

section NegativeCompWitness

/-- Stateless machine doubling `w ↦ w ++ w` (replies `≤ 2 * |w|`, not `Machine.IsReplyBounded`). -/
private def doubleMachine :
    ℕ → Finset (Fin 2) → Machine OracleSpec.empty (netSpec (List Bool) (List Bool)) :=
  fun _ _ =>
    { State := PUnit, init := pure PUnit.unit, handle := fun w _ => pure (w ++ w, PUnit.unit) }

/-- `doubleMachine` is strict PPT (`Machine.IsPPTFamily`). -/
theorem doubleMachine_isPPT :
    Machine.IsPPTFamily doubleMachine WordInterface.empty (WordInterface.net msgPort) := by
  let Arg := PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool
  let EIn := encHandlerCall (encPPTParam 2) (encFinite (WordInterface.net msgPort).Channel) encBits
  have hword : ComputableInPolyTime (fun x : Arg => x.2.1.2) EIn encBits := by
    unfold EIn encHandlerCall; fun_prop
  have hdouble : ComputableInPolyTime (fun x : Arg => (x.2.1.2 ++ x.2.1.2, encUnit ()))
      EIn (encPair encBits encBits) :=
    (ComputableInPolyTime.bitsAppend hword hword).prod (ComputableInPolyTime.const (encUnit ()))
  refine ⟨{
    codec := fun _ _ => punitCodec
    init := (ComputableInPolyTime.const (encUnit ())).isPPTOn
    handle := by
      refine (hdouble.isOraclePPTOn (Operation := WordInterface.empty.Channel)).congr
        fun x State oracle s => ?_
      rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
      simp only [wordHandle, doubleMachine, punitCodec, StateT.run, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure, ProbOracleComp.runWith_pure]; rfl
    normalize := ComputableInPolyTime.const (encUnit ())
    growth := fun _ _ => 0
    growth_poly := PolyBounded.const 0
    preserve _ _ s out hout := by
      cases s
      simp only [wordHandle, doubleMachine, StateT.run, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure, OracleComp.support] at hout
      rcases hout with rfl; exact le_rfl }⟩

/-- `doubleMachine` is not `Machine.IsReplyBounded` (even though replies are at most `2 * |w|`). -/
theorem doubleMachine_not_isReplyBounded :
    ¬ Machine.IsReplyBounded doubleMachine WordInterface.empty (WordInterface.net msgPort) := by
  rintro ⟨bound, _, hle⟩
  let p : PPTParam 2 := ⟨0, 0, ∅⟩
  let w : List Bool := List.replicate (bound p + 1) true
  have hmem : (w ++ w, PUnit.unit) ∈ OracleComp.support (ProbOracleComp.lowerWith
      WordInterface.empty p.replyBound (((doubleMachine 0 ∅).handle w).run PUnit.unit)) := by
    simp only [doubleMachine, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_pure,
      OracleComp.support, OracleComp.supportWith_pure]; rfl
  have hlen := hle p w PUnit.unit (w ++ w, PUnit.unit) hmem
  change (msgPort.reply (w ++ w)).length ≤ bound p at hlen
  simp only [msgPort, encBits_apply, List.length_append, w, List.length_replicate] at hlen; omega

/-- Stateless outer machine making `κ` sequential queries and returning the final reply. -/
private def iterQueryMachine :
    ℕ → Finset (Fin 2) →
      Machine (netSpec (List Bool) (List Bool)) (netSpec (List Bool) (List Bool)) :=
  fun κ _ =>
    { State := PUnit
      init := pure PUnit.unit
      handle := fun w _ => (·, PUnit.unit) <$>
        OracleComp.iterate κ
          (fun x => ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x) w }

private theorem lowerWith_iterate_net (limit k : ℕ) (w : List Bool) :
    ProbOracleComp.lowerWith (WordInterface.net msgPort) limit
        (OracleComp.iterate k (fun x => ProbOracleComp.query
          (spec := netSpec (List Bool) (List Bool)) x) w) =
      OracleComp.iterate k (fun x => ProbOracleComp.lowerWith (WordInterface.net msgPort) limit
        (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x)) w := by
  rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
    OracleComp.interpret_iterate]; rfl

/-- `iterQueryMachine` is strict PPT (`Machine.IsPPTFamily`). -/
theorem iterQueryMachine_isPPT :
    Machine.IsPPTFamily iterQueryMachine
      (WordInterface.net msgPort) (WordInterface.net msgPort) := by
  let Arg := PPTParam 2 × ((WordInterface.net msgPort).Channel × List Bool) × List Bool
  let EIn := encHandlerCall (encPPTParam 2) (encFinite (WordInterface.net msgPort).Channel) encBits
  have hrc : ComputableInPolyTime (fun x : Arg => x.1.replyBound) EIn encUnary := by
    unfold EIn encHandlerCall; fun_prop
  have hstep : IsOraclePPTOn (encPair EIn encBits) encBits
      (fun pair : Arg × List Bool =>
        ProbOracleComp.lowerWith (WordInterface.net msgPort) pair.1.1.replyBound
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) pair.2)) :=
    ((WordInterface.net msgPort).isOraclePPTOn_lowerWith_decodeQuery (input := encPair EIn encBits)
      (ch := fun _ => ()) (word := fun pair => pair.2) (limit := fun pair => pair.1.1.replyBound)
      (ComputableInPolyTime.const ()) (ComputableInPolyTime.snd EIn encBits)
      (hrc.comp (ComputableInPolyTime.fst EIn encBits))).congr fun _ _ _ _ => rfl
  have hloop : IsOraclePPTOn EIn encBits
      (fun x : Arg => OracleComp.iterate x.1.secParam
        (fun state => ProbOracleComp.lowerWith (WordInterface.net msgPort) x.1.replyBound
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) state))
        (msgPort.queryDecoder.decode x.2.1.2)) := by
    refine IsOraclePPTOn.iterateWith_of_bounded_growth
      (by unfold EIn encHandlerCall; fun_prop)
      (msgPort.queryDecoder.computableInPolyTime.comp (by unfold EIn encHandlerCall; fun_prop))
      hstep (by simpa only [encUnary_apply, List.length_replicate] using hrc.polyBounded_length)
      fun x state next hnext => ?_
    simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, WordInterface.lowerQuery,
      WordInterface.net, msgPort, Decoder.bits, id_eq] at hnext
    rcases OracleComp.mem_supportWith_map_iff.mp hnext with ⟨t, ht, rfl⟩
    rcases OracleComp.mem_supportWith_map_iff.mp ht with ⟨w, _, rfl⟩
    simp only [encBits_apply, id_eq, List.length_take]; omega
  refine ⟨{
    codec := fun _ _ => punitCodec
    init := (ComputableInPolyTime.const (encUnit ())).isPPTOn
    handle := by
      have hp := hloop.map ((by fun_prop : ComputableInPolyTime id encBits encBits).prod
        (ComputableInPolyTime.const (encIn := encBits) (encOut := encBits) (encUnit ())))
      refine hp.congr fun x State oracle s => ?_
      rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
      change ProbOracleComp.runWith oracle ((fun a => (a, encUnit ())) <$>
          OracleComp.iterate p.secParam (fun state => ProbOracleComp.lowerWith
            (WordInterface.net msgPort) p.replyBound (ProbOracleComp.query
              (spec := netSpec (List Bool) (List Bool)) state)) (msgPort.queryDecoder.decode w)) s =
        ProbOracleComp.runWith oracle (wordHandle iterQueryMachine (WordInterface.net msgPort)
          (WordInterface.net msgPort) (fun _ _ => punitCodec) p ((), w) sw) s
      have hwh : wordHandle iterQueryMachine (WordInterface.net msgPort) (WordInterface.net msgPort)
          (fun _ _ => punitCodec) p ((), w) sw =
          (fun a => (msgPort.reply a, punitCodec.enc PUnit.unit)) <$>
            ProbOracleComp.lowerWith (WordInterface.net msgPort) p.replyBound (OracleComp.iterate
              p.secParam (fun x => ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x)
              (msgPort.queryDecoder.decode w)) := by
        simp only [wordHandle, iterQueryMachine, StateT.run, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_map, Functor.map_map]; rfl
      rw [hwh, lowerWith_iterate_net]; rfl
    normalize := ComputableInPolyTime.const (encUnit ())
    growth := fun _ _ => 0
    growth_poly := PolyBounded.const 0
    preserve _ _ s out hout := by
      cases s
      simp only [wordHandle, iterQueryMachine, StateT.run, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_map, OracleComp.support, OracleComp.supportWith_map,
        Set.mem_image] at hout
      rcases hout with ⟨⟨_, ⟨⟩⟩, _, rfl⟩; exact le_rfl }⟩

/-- `iterQueryMachine` is `Machine.IsRequestBounded` with bound `pw.2.length + pw.1.replyBound`. -/
theorem iterQueryMachine_isRequestBounded :
    Machine.IsRequestBounded iterQueryMachine
      (WordInterface.net msgPort) (WordInterface.net msgPort) := by
  have hqs : ∀ (limit k B : ℕ) (w : List Bool), w.length ≤ B → limit ≤ B →
      OracleComp.QueriesSatisfy
        (fun op => Sum.elim (fun _ => True)
          (fun cw : (WordInterface.net msgPort).Channel × List Bool => cw.2.length ≤ B) op)
        (OracleComp.iterate k (fun x => ProbOracleComp.lowerWith (WordInterface.net msgPort) limit
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) x)) w) := by
    intro limit k B w hw hlim
    induction k generalizing w with
    | zero => exact OracleComp.QueriesSatisfy.pure w
    | succ k ih =>
      have hstep : ProbOracleComp.lowerWith (WordInterface.net msgPort) limit
          (ProbOracleComp.query (spec := netSpec (List Bool) (List Bool)) w) =
          (fun raw => Decoder.bits.decode (List.take limit raw)) <$>
            ProbOracleComp.query (spec := fun _ : (WordInterface.net msgPort).Channel × List Bool =>
              List Bool) ((), encBits w) := rfl
      rw [OracleComp.iterate_succ_bind, hstep, map_eq_bind_pure_comp, bind_assoc]
      simp only [pure_bind, Function.comp_apply]
      exact OracleComp.QueriesSatisfy.bind (OracleComp.QueriesSatisfy.query hw) fun raw =>
        ih (Decoder.bits.decode (List.take limit raw))
          (le_trans (List.length_take_le _ _) hlim)
  have hrb : PolyBounded
      (fun pw : PPTParam 2 × List Bool => (encPair (encPPTParam 2) encBits pw).length)
      (fun pw => pw.2.length + pw.1.replyBound) := by
    have hlen : ComputableInPolyTime (fun pw : PPTParam 2 × List Bool => pw.2.length)
        (encPair (encPPTParam 2) encBits) encUnary := by
      simpa only [encBits_apply, Function.comp_def] using
        (ComputableInPolyTime.encoding_length encBits).comp
          (ComputableInPolyTime.snd (encPPTParam 2) encBits)
    have h1 := ComputableInPolyTime.unary_add.comp (hlen.prod (by fun_prop : ComputableInPolyTime
      (fun pw : PPTParam 2 × List Bool => pw.1.replyBound) (encPair (encPPTParam 2) encBits)
      encUnary))
    simpa only [encUnary_apply, List.length_replicate, Function.comp_def] using
      h1.polyBounded_length
  refine ⟨fun pw => pw.2.length + pw.1.replyBound, hrb, fun p q s => ?_⟩
  simp only [iterQueryMachine, StateT.run, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_map, OracleComp.queriesSatisfy_map_iff]
  rw [← ProbOracleComp.lowerWith, lowerWith_iterate_net]
  exact hqs p.replyBound p.secParam (q.length + p.replyBound) q (Nat.le_add_right _ _)
    (Nat.le_add_left _ _)

/-- `iterQueryMachine κ C` has per-activation call budget `κ + 1`. -/
theorem iterQueryMachine_isBounded (κ : ℕ) (C : Finset (Fin 2)) :
    (iterQueryMachine κ C).IsBounded (κ + 1) := by
  refine ⟨(OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _), fun q s => ?_⟩
  simp only [iterQueryMachine, StateT.run, OracleComp.isCostBounded_map_iff]
  have hiter : ∀ k w, (OracleComp.iterate k (fun x => ProbOracleComp.query
      (spec := netSpec (List Bool) (List Bool)) x) w).IsQueryBounded k := fun k => by
    induction k with
    | zero => intro w; exact OracleComp.IsCostBounded.pure w 0
    | succ k ih =>
      intro w; rw [OracleComp.iterate_succ]
      exact OracleComp.IsCostBounded.bind (ih w)
        (fun a => OracleComp.IsCostBounded.query (q := Sum.inr a))
  exact (hiter κ q).mono (Nat.le_succ κ)

private theorem exists_poly_lt_two_pow (c d : ℕ) : ∃ κ, c * (κ + 1) ^ d < 2 ^ κ := by
  have hsq : ∀ m : ℕ, (m + 4) ^ 2 ≤ 2 ^ (m + 6) := by
    intro m; induction m with
    | zero => decide
    | succ m ih =>
      have : 2 * m + 9 ≤ (m + 4) ^ 2 := by nlinarith
      calc (m + 1 + 4) ^ 2 = (m + 4) ^ 2 + (2 * m + 9) := by ring
        _ ≤ 2 ^ (m + 6) + 2 ^ (m + 6) := Nat.add_le_add ih (this.trans ih)
        _ = 2 ^ (m + 1 + 6) := by rw [pow_succ]; ring
  let k : ℕ := 2 * d + c + 6
  refine ⟨2 ^ k, ?_⟩
  have hbase : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    have := Nat.one_le_pow k 2 (by decide)
    calc 2 ^ k + 1 ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left this _
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hexp : c + (k + 1) * d ≤ 2 ^ k :=
    (show c + (k + 1) * d ≤ (2 * d + c + 4) ^ 2 by dsimp only [k]; nlinarith).trans
      (hsq (2 * d + c))
  calc c * (2 ^ k + 1) ^ d < 2 ^ c * (2 ^ (k + 1)) ^ d :=
      Nat.mul_lt_mul_of_lt_of_le (Nat.lt_pow_self (by decide : 1 < 2))
        (Nat.pow_le_pow_left hbase d) (Nat.pow_pos (Nat.pow_pos (by decide : 0 < 2)))
    _ = 2 ^ (c + (k + 1) * d) := by rw [← pow_mul, mul_comm (k + 1) d, ← pow_add]
    _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by decide) hexp

/-- Negative witness: omitting `Machine.IsReplyBounded` makes sequential composition closure
false (`¬ Machine.IsPPTFamily (fun κ C => (iterQueryMachine κ C).comp (doubleMachine κ C))`), even
though `doubleMachine` is PPT (replies `≤ 2 * |w|`) and `iterQueryMachine` is PPT,
request-bounded, and call-bounded (`κ + 1`). -/
theorem negative_comp_not_isPPT :
    ¬ Machine.IsPPTFamily (fun κ C => (iterQueryMachine κ C).comp (doubleMachine κ C))
      WordInterface.empty (WordInterface.net msgPort) := by
  rintro ⟨cert⟩
  obtain ⟨c0, d0, hinit⟩ := cert.init.length_le
  obtain ⟨c1, d1, hhandle⟩ := cert.handle.length_le
  have hp : ComputableInPolyTime (fun κ : ℕ => (⟨κ, 0, ∅⟩ : PPTParam 2))
      encUnary (encPPTParam 2) := by
    have : ComputableInPolyTime (fun _ : ℕ => (∅ : Finset (Fin 2)))
        encUnary (encFinite (Finset (Fin 2))) := ComputableInPolyTime.const ∅
    fun_prop
  obtain ⟨cp, dp, hcp⟩ := hp.polyBounded_length.exists_le
  let D := max dp (dp * d0)
  let M0 := cp + 1
  let Minit := c0 * M0 ^ d0
  let Mchan := Nat.card (WordInterface.net msgPort).Channel
  let A := 2 * M0 + 4 * (Mchan + 2) + Minit + 6
  obtain ⟨κ, hκ⟩ := exists_poly_lt_two_pow (c1 * (A + 1) ^ d1) (D * d1)
  let p : PPTParam 2 := ⟨κ, 0, ∅⟩
  let s0 : ((iterQueryMachine κ ∅).comp (doubleMachine κ ∅)).State := (PUnit.unit, PUnit.unit)
  have hmono (c a d D k : ℕ) (ha : a ≤ c * (k + 1) ^ d) (hd : d ≤ D) :
      a + 1 ≤ (c + 1) * (k + 1) ^ D := by
    calc a + 1 ≤ c * (k + 1) ^ D + (k + 1) ^ D :=
        Nat.add_le_add (ha.trans (Nat.mul_le_mul_left c
          (Nat.pow_le_pow_right (Nat.succ_pos k) hd))) (Nat.one_le_pow D (k + 1) (Nat.succ_pos k))
      _ = (c + 1) * (k + 1) ^ D := by simp [Nat.add_mul]
  have hlenP : (encPPTParam 2 p).length ≤ cp * (κ + 1) ^ dp := by
    simpa only [encUnary_apply, List.length_replicate] using hcp κ
  have hlenP' := hmono cp _ dp D κ hlenP (le_max_left _ _)
  have hmemInit : (cert.codec κ ∅).enc s0 ∈ (ProbComp.eval ((cert.codec κ ∅).enc <$>
      ((iterQueryMachine κ ∅).comp (doubleMachine κ ∅)).init)).support := by
    change (cert.codec κ ∅).enc s0 ∈ (ProbComp.eval ((cert.codec κ ∅).enc <$>
      (pure s0 : ProbComp _))).support
    rw [map_pure, ProbComp.eval_pure]; exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have hlenInit : ((cert.codec κ ∅).enc s0).length ≤ Minit * (κ + 1) ^ D := by
    have h2 : c0 * (M0 * (κ + 1) ^ dp) ^ d0 = Minit * (κ + 1) ^ (dp * d0) := by
      rw [mul_pow, ← pow_mul, mul_assoc]
    exact (hinit p _ hmemInit).trans ((Nat.mul_le_mul_left c0
      (Nat.pow_le_pow_left (hmono cp _ dp dp κ hlenP (le_refl dp)) d0)).trans
      (h2 ▸ Nat.mul_le_mul_left Minit (Nat.pow_le_pow_right (Nat.succ_pos κ) (le_max_right _ _))))
  have hrun (k : ℕ) (x : List Bool) : (doubleMachine κ ∅).runFrom
      (OracleComp.iterate k (fun w => ProbOracleComp.query
        (spec := netSpec (List Bool) (List Bool)) w) x) (PUnit.unit : (doubleMachine κ ∅).State) =
      pure (Nat.iterate (fun w => w ++ w) k x, (PUnit.unit : (doubleMachine κ ∅).State)) := by
    dsimp only [doubleMachine]; induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [OracleComp.iterate_succ, Machine.runFrom_bind, ih x, pure_bind, Machine.runFrom_query]
      simp only [StateT.run, Function.iterate_succ_apply']
  have hcompHandle : ((iterQueryMachine κ ∅).comp (doubleMachine κ ∅)).handle [true] s0 =
      pure (Nat.iterate (fun w => w ++ w) κ [true], s0) := by
    change Equiv.prodAssoc _ _ _ <$> (doubleMachine κ ∅).runFrom ((·, PUnit.unit) <$>
      OracleComp.iterate κ (fun x => ProbOracleComp.query
        (spec := netSpec (List Bool) (List Bool)) x) [true]) PUnit.unit = _
    dsimp only [doubleMachine] at hrun ⊢; rw [Machine.runFrom_map, hrun κ [true], map_pure]; rfl
  let ch0 : (WordInterface.net msgPort).Channel := ()
  let x := (p, (ch0, [true]), (cert.codec κ ∅).enc s0)
  have hmemHandle : ((Nat.iterate (fun w => w ++ w) κ [true], (cert.codec κ ∅).enc s0), ()) ∈
      (ProbOracleComp.runWith emptyWordOracle
        (wordHandle (fun κ C => (iterQueryMachine κ C).comp (doubleMachine κ C))
          WordInterface.empty (WordInterface.net msgPort) cert.codec x.1 x.2.1 x.2.2)
        ()).support := by
    dsimp only [wordHandle, WordInterface.net, WordInterface.decodeQuery, WordInterface.reply,
      msgPort, Decoder.bits, id_eq, StateT.run, x, p]
    rw [(cert.codec κ ∅).decode_enc, hcompHandle, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_pure, map_pure, ProbOracleComp.runWith_pure]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have hlen2 (k : ℕ) (w : List Bool) :
      (Nat.iterate (fun u => u ++ u) k w).length = 2 ^ k * w.length := by
    induction k generalizing w with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply, ih (w ++ w), List.length_append, pow_succ]; ring
  have h2pow : 2 ^ κ ≤ (encPair encBits encBits
      (Nat.iterate (fun w => w ++ w) κ [true], (cert.codec κ ∅).enc s0)).length := by
    have h := hlen2 κ [true]; simp only [List.length_singleton, Nat.mul_one] at h
    simp only [length_encPair, encBits_apply]; omega
  have hxlen : (encHandlerCall (encPPTParam 2) (encFinite (WordInterface.net msgPort).Channel)
      encBits x).length + 1 ≤ A * (κ + 1) ^ D := by
    have hch := (length_encFinite_lt ch0).le
    have hc := Nat.le_mul_of_pos_right (4 * (Mchan + 2) + 6) (Nat.one_le_pow D (κ + 1)
      (Nat.succ_pos κ))
    simp only [encHandlerCall, length_encPair, encBits_apply, x]
    have h1 : ([true] : List Bool).length = 1 := rfl
    have : 2 * (encPPTParam 2 p).length + 1 + (2 * (2 * (encFinite
        (WordInterface.net msgPort).Channel ch0).length + 1 + ([true] : List Bool).length) + 1 +
          ((cert.codec κ ∅).enc s0).length) + 1 ≤
        2 * (M0 * (κ + 1) ^ D) + (4 * (Mchan + 2) + Minit * (κ + 1) ^ D + 6) := by
      dsimp only [M0] at hlenP' ⊢; omega
    nlinarith [show A = 2 * M0 + 4 * (Mchan + 2) + Minit + 6 from rfl]
  have hbound := h2pow.trans (hhandle x Unit emptyWordOracle () () _ hmemHandle)
  have hfin : c1 * ((encHandlerCall (encPPTParam 2) (encFinite (WordInterface.net msgPort).Channel)
      encBits x).length + 1) ^ d1 ≤ c1 * (A + 1) ^ d1 * (κ + 1) ^ (D * d1) := by
    have hpowD1 := Nat.pow_le_pow_left (hxlen.trans (Nat.mul_le_mul_right _ (Nat.le_succ A))) d1
    rw [mul_pow, ← pow_mul, Nat.succ_eq_add_one] at hpowD1
    exact (Nat.mul_le_mul_left c1 hpowD1).trans (by rw [mul_assoc])
  exact Nat.lt_irrefl _ ((hbound.trans hfin).trans_lt hκ)

end NegativeCompWitness

end CslibFrontierTests.Crypto.UCPPTLink
