/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Protocols.UC.PPT.Execution
import CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers
import CslibFrontierTests.Crypto.UCPPTLink
import CslibFrontierTests.Crypto.UCPPTWrappers

/-!
# Tests for `UC.PPT.Execution`

End-to-end execution witnesses for `CslibFrontier.Crypto.Protocols.UC.PPT.Execution`:

1. `windowEnv` writes `(0, true)` and polls `(1, false)`, outputting `decide (polled ≠ some [])`.
   `windowExec_isPPT` instantiates `isPPT_exec`, `Environment.IsPPT.isPPT_run`, and
   `Machine.isReplyBounded_id`; `windowExec_eval` checks that the output law is
   `PMF.pure (decide (0 < κ))`.
2. `relayHybrid`, `relayEnv`, `relayEnv_absorbHybrid_isPPT`, and `relayCompose_window_exec_isPPT`:
   a counter-bearing forwarding hybrid protocol `relayHybrid` (reusing `unaryCodec`,
   `computable_normalize_unary`, and `isOraclePPTOn_forwardAndIncUnary` from `UCPPTWrappers`)
   is certified for `HybridProtocol.IsPPT`, `Machine.IsReplyBounded`, `hybridWrap` transfers,
   `absorbHybrid`, and dummy-adversary execution `compose relayHybrid windowProtocol` with
   `κ`-dependent output `PMF.pure (decide (0 < κ))` (`relayCompose_window_exec_eval`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPPTExecution

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.UCPPT CslibFrontierTests.Crypto.UCPPTLink
open CslibFrontierTests.Crypto.UCPPTWrappers

/-! ### 1. Shared write-then-poll environment and `windowProtocol` execution -/

/-- Environment writing `(0, true)` and polling `(1, false)`, returning
`decide (polled ≠ some [])`. -/
private def writePollEnv {AdvQ AdvR : Type} : Environment 2 Bool (List Bool) AdvQ AdvR :=
  fun _ _ => do
    let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), true))
    let polled ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), false))
    return decide (polled ≠ some [])

/-- `writePollEnv` is uniform strict oracle PPT (`Environment.IsPPT`) for any adversary port. -/
private theorem writePollEnv_isPPT {AdvQ AdvR : Type} (adv : WordPort AdvQ AdvR) :
    (writePollEnv (AdvQ := AdvQ) (AdvR := AdvR)).IsPPT coinPartyPort adv := by
  let iE := WordInterface.exec coinPartyPort adv
  let sp := execSpec 2 Bool (List Bool) AdvQ AdvR
  have hq (q : (Fin 2 × Bool) ⊕ AdvQ) :
      IsOraclePPTOn encEnvParam encBits fun e : EnvParam =>
        iE.reply q <$> ProbOracleComp.lowerWith iE e.replyBound
          (ProbOracleComp.query (spec := sp) q) :=
    iE.isOraclePPTOn_lowerWith_query (query := fun _ => q) (limit := EnvParam.replyBound)
      (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) (by fun_prop)
  have hpost : ComputableInPolyTime
      (fun w : List Bool => decide (coinPartyPort.replyDecoder.decode w ≠ some []))
      encBits encBool := by
    have hpos : ComputableInPolyTime (fun k : ℕ => decide (0 < k)) encUnary encBool := by fun_prop
    have hlist : ComputableInPolyTime
        (fun w : List Bool => (coinPartyPort.replyDecoder.decode w).getD [true]) encBits encBits :=
      (ComputableInPolyTime.optionGetD encBits).comp
        (coinPartyPort.replyDecoder.computableInPolyTime.prod (ComputableInPolyTime.const [true]))
    have heq : ((fun k : ℕ => decide (0 < k)) ∘ (fun l : List Bool => (encBits l).length) ∘
        fun w : List Bool => (coinPartyPort.replyDecoder.decode w).getD [true]) =
        fun w : List Bool => decide (coinPartyPort.replyDecoder.decode w ≠ some []) := by
      funext w; simp only [Function.comp_apply, encBits_apply, decide_eq_decide]
      rcases coinPartyPort.replyDecoder.decode w with _ | ⟨_ | ⟨_, _⟩⟩ <;> simp
    exact heq ▸ hpos.comp ((ComputableInPolyTime.encoding_length encBits).comp hlist)
  let qPoll : (Fin 2 × Bool) ⊕ AdvQ := Sum.inl ((1 : Fin 2), false)
  have h12 := (hq (Sum.inl ((0 : Fin 2), true))).bind_with
    (second := fun e _ => iE.reply qPoll <$> ProbOracleComp.lowerWith iE e.replyBound
      (ProbOracleComp.query qPoll))
    ((hq qPoll).preprocess (ComputableInPolyTime.fst encEnvParam encBits))
  have hdec (r : Option (List Bool)) :
      coinPartyPort.replyDecoder.decode (iE.reply (Sum.inl ((1 : Fin 2), false)) r) = r :=
    coinPartyPort.replyDecoder.decode_enc r
  refine (h12.map hpost).congr fun e State oracle s => ?_
  simp only [writePollEnv, iE, qPoll, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, hdec]

/-- Environment writing `(0, true)` and polling `(1, false)`, returning
`decide (polled ≠ some [])`. -/
private def windowEnv :
    Environment 2 Bool (List Bool) (RoutedNetQ 2 Bool Unit) (RoutedNetR (List Bool) Unit) :=
  writePollEnv

/-- `windowEnv` is uniform strict oracle PPT (`Environment.IsPPT`). -/
theorem windowEnv_isPPT :
    windowEnv.IsPPT coinPartyPort (WordPort.sum coinPartyPort unitPort) :=
  writePollEnv_isPPT _

/-- End-to-end execution of `windowProtocol`, `dummyAdversary`, and `windowEnv` is `IsPPT`. -/
theorem windowExec_isPPT :
    Cslib.Probability.IsPPT encBool
      (fun κ z => exec windowProtocol (dummyAdversary 2 _ _) ∅ windowEnv κ z) :=
  isPPT_exec (WordPort.computable_partyIndex coinInputPort) windowProtocol_isPPT
    windowProtocol_isReplyBounded (Adversary.isPPT_dummyAdversary 2 _)
    (Machine.isReplyBounded_id _) windowEnv_isPPT ∅

/-- Observable, `κ`-dependent execution output: party `0` stores `[true ^^ c]` and party `1` polls
`take κ [true ^^ c]`, which is non-empty iff `0 < κ`. -/
theorem windowExec_eval (κ : ℕ) (z : List Bool) :
    ProbComp.eval (exec windowProtocol (dummyAdversary 2 _ _) ∅ windowEnv κ z) =
      PMF.pure (decide (0 < κ)) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [exec_dummyAdversary]
  simp only [Machine.run, Machine.link, windowEnv, writePollEnv, corruptRouter, windowProtocol,
    ProbOracleComp.sample_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
    StateT.run, Finset.notMem_empty, ↓reduceIte, h10, Machine.closeProgram_bind,
    Machine.closeProgram_sample, Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_pure]
  have htake (c : Bool) : decide (some (List.take κ [true ^^ c]) ≠ some []) = decide (0 < κ) := by
    cases κ <;> rfl
  simp only [htake, PMF.bind_const]

/-! ### 2. Hybrid protocol and subroutine absorption (`relayHybrid`, `relayEnv`) -/

/-- Counter-bearing forwarding hybrid protocol relaying every party call to the subroutine's party
port and answering network queries trivially. -/
private def relayHybrid : HybridProtocol 2 Bool (List Bool) Unit Unit Bool (List Bool) :=
  fun _ _ =>
    { State := ℕ
      init := pure 0
      handle := fun
        | Sum.inl (i, b), c => do
          let r ← ProbOracleComp.query (spec := netSpec (Fin 2 × Bool) (Option (List Bool))) (i, b)
          pure (r, c + 1)
        | Sum.inr (), c => pure ((), c) }

private theorem relayHybrid_wordHandle_inl (p : PPTParam 2) (w sw : List Bool) :
    wordHandle relayHybrid (WordInterface.net coinPartyPort)
        (WordInterface.protocol coinPartyPort unitPort) (fun _ _ => unaryCodec) p (.inl (), w) sw =
      (fun r => (r, encUnary (Decoder.unary.decode sw + 1))) <$>
        ((WordInterface.net coinPartyPort).reply
            ((WordInterface.net coinPartyPort).decodeQuery () w) <$>
          ProbOracleComp.lowerWith (WordInterface.net coinPartyPort) p.replyBound
            (ProbOracleComp.query ((WordInterface.net coinPartyPort).decodeQuery () w))) := by
  simp only [wordHandle, relayHybrid, unaryCodec, WordInterface.protocol, WordInterface.sum,
    WordInterface.net, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_pure]
  rfl

private def relayHybridCert :
    PPTCertificate relayHybrid (WordInterface.net coinPartyPort)
      (WordInterface.protocol coinPartyPort unitPort) where
  codec _ _ := unaryCodec
  init := by
    change IsPPTOn (encPPTParam 2) encBits (fun _ => pure (encUnary 0))
    exact (ComputableInPolyTime.const (encUnary 0)).isPPTOn
  handle := by
    let iP := WordInterface.protocol coinPartyPort unitPort
    let EIn := encHandlerCall (encPPTParam 2) (encFinite iP.Channel) encBits
    have htag : ComputableInPolyTime
        (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool => x.2.1.1)
        EIn (encFinite iP.Channel) := by
      unfold EIn encHandlerCall; fun_prop
    have hparty : IsOraclePPTOn (Operation := (WordInterface.net coinPartyPort).Channel)
        EIn (encPair encBits encBits)
        (fun x => wordHandle relayHybrid (WordInterface.net coinPartyPort) iP
          (fun _ _ => unaryCodec) x.1 (.inl (), x.2.1.2) x.2.2) := by
      refine (isOraclePPTOn_forwardAndIncUnary (n := 2) (chOut := iP.Channel)
        (WordInterface.net coinPartyPort) ()).congr fun x State oracle s => ?_
      rcases x with ⟨p, ⟨_, w⟩, sw⟩
      rw [relayHybrid_wordHandle_inl]
    have hnet : IsOraclePPTOn (Operation := (WordInterface.net coinPartyPort).Channel)
        EIn (encPair encBits encBits)
        (fun x => wordHandle relayHybrid (WordInterface.net coinPartyPort) iP
          (fun _ _ => unaryCodec) x.1 (.inr (), x.2.1.2) x.2.2) := by
      have hpair : ComputableInPolyTime
          (fun x : PPTParam 2 × (iP.Channel × List Bool) × List Bool => (x.1, x.2.2))
          EIn (encPair (encPPTParam 2) encBits) := by
        unfold EIn encHandlerCall; fun_prop
      refine ((ComputableInPolyTime.const (unitPort.reply ())).prod
        ((computable_normalize_unary 2).comp hpair)).isPPTOn.isOraclePPTOn.congr
        fun x State oracle s => ?_
      rcases x with ⟨p, ⟨_, w⟩, sw⟩
      simp only [wordHandle, relayHybrid, iP, WordInterface.protocol, WordInterface.sum,
        WordInterface.net, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_pure]
      rfl
    let branch : iP.Channel → PPTParam 2 × (iP.Channel × List Bool) × List Bool →
        WordOracleComp (WordInterface.net coinPartyPort).Channel (List Bool × List Bool) :=
      fun ch x => wordHandle relayHybrid (WordInterface.net coinPartyPort) iP
        (fun _ _ => unaryCodec) x.1 (ch, x.2.1.2) x.2.2
    refine (IsOraclePPTOn.finite_cases (branch := branch) htag ?_).congr
      fun x State oracle s => ?_
    · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
      · exact hparty
      · exact hnet
    · rfl
  normalize := computable_normalize_unary 2
  growth _ _ := 1
  growth_poly := PolyBounded.const 1
  preserve p req s out hout := by
    let s' : ℕ := s
    rcases req with ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, w⟩
    · rw [relayHybrid_wordHandle_inl] at hout
      simp only [OracleComp.mem_supportWith_map_iff] at hout
      rcases hout with ⟨_, _, rfl⟩
      change (encUnary (Decoder.unary.decode (encUnary s') + 1)).length ≤ (encUnary s').length + 1
      rw [Decoder.unary.decode_enc s']
      simp only [encUnary_apply, List.length_replicate, le_refl]
    · simp only [wordHandle, relayHybrid, unaryCodec, WordInterface.protocol, WordInterface.sum,
        WordInterface.net, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_pure,
        OracleComp.support] at hout
      rcases OracleComp.mem_supportWith_map_iff.mp hout with ⟨y, hy, rfl⟩
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hy
      change (encUnary (Decoder.unary.decode (encUnary s'))).length ≤ (encUnary s').length + 1
      rw [Decoder.unary.decode_enc s']
      exact Nat.le_add_right _ _

/-- `relayHybrid` is strict PPT (`HybridProtocol.IsPPT`). -/
theorem relayHybrid_isPPT : relayHybrid.IsPPT coinPartyPort unitPort coinPartyPort :=
  ⟨relayHybridCert⟩

/-- `relayHybrid` is `Machine.IsReplyBounded`, reusing `exists_polyBounded_reply_take`. -/
theorem relayHybrid_isReplyBounded :
    Machine.IsReplyBounded relayHybrid (WordInterface.net coinPartyPort)
      (WordInterface.protocol coinPartyPort unitPort) := by
  obtain ⟨bound, hpoly, hle⟩ :=
    (WordInterface.net coinPartyPort).exists_polyBounded_reply_take (n := 2)
  refine ⟨bound, hpoly, fun p q s x hx => ?_⟩
  let s' : ℕ := s
  rcases q with qp | ⟨⟩
  · change x ∈ OracleComp.support (ProbOracleComp.lowerWith (WordInterface.net coinPartyPort)
      p.replyBound ((fun r => (r, s' + 1)) <$> ProbOracleComp.query qp)) at hx
    rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_map] at hx
    obtain ⟨y, hy, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hx
    simp only [ProbOracleComp.simulate_query, WordInterface.lowerQuery,
      OracleComp.mem_supportWith_map_iff, ProbOracleComp.supportWith_query, Set.mem_univ,
      true_and] at hy
    obtain ⟨w, ⟨a, rfl⟩, rfl⟩ := hy
    simpa only [WordInterface.protocol, WordInterface.sum, WordInterface.net] using hle p qp a
  · simp only [relayHybrid, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_pure,
      OracleComp.support] at hx
    obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx
    simp only [WordInterface.protocol, WordInterface.sum, WordInterface.net, unitPort,
      encUnit_apply, List.length_nil, Nat.zero_le]

/-- `hybridWrap` preserves `IsPPTFamily` for `relayHybrid`. -/
theorem relayHybrid_hybridWrap_isPPT :
    Machine.IsPPTFamily (fun κ C => hybridWrap (NQ := Unit) (NR := Unit) (relayHybrid κ C))
      (WordInterface.protocol coinPartyPort unitPort)
      (WordInterface.protocol coinPartyPort (WordPort.sum unitPort unitPort)) :=
  relayHybrid_isPPT.hybridWrap (nq := unitPort)

/-- `hybridWrap` preserves `Machine.IsReplyBounded` for `relayHybrid`. -/
theorem relayHybrid_hybridWrap_isReplyBounded :
    Machine.IsReplyBounded (fun κ C => hybridWrap (NQ := Unit) (NR := Unit) (relayHybrid κ C))
      (WordInterface.protocol coinPartyPort unitPort)
      (WordInterface.protocol coinPartyPort (WordPort.sum unitPort unitPort)) :=
  relayHybrid_isReplyBounded.hybridWrap (nq := unitPort)

/-- Environment for `compose relayHybrid windowProtocol` writing `(0, true)` and polling
`(1, false)`. -/
private def relayEnv :
    Environment 2 Bool (List Bool)
      (RoutedNetQ 2 Bool (Unit ⊕ RoutedNetQ 2 Bool Unit))
      (RoutedNetR (List Bool) (Unit ⊕ RoutedNetR (List Bool) Unit)) :=
  writePollEnv

/-- `relayEnv` is uniform strict oracle PPT (`Environment.IsPPT`). -/
theorem relayEnv_isPPT :
    relayEnv.IsPPT coinPartyPort
      (WordPort.sum coinPartyPort (WordPort.sum unitPort (WordPort.sum coinPartyPort unitPort))) :=
  writePollEnv_isPPT _

/-- Absorbing `relayHybrid` into `relayEnv` preserves `Environment.IsPPT`. -/
theorem relayEnv_absorbHybrid_isPPT :
    (absorbHybrid {1} relayHybrid relayEnv).IsPPT coinPartyPort
      (WordPort.sum coinPartyPort unitPort) :=
  relayEnv_isPPT.absorbHybrid (WordPort.computable_partyIndex coinInputPort)
    relayHybrid_isPPT relayHybrid_isReplyBounded {1}

/-- End-to-end execution of `compose relayHybrid windowProtocol` with `dummyAdversary` and
`relayEnv` is `IsPPT`, without `Machine.comp` closure. -/
theorem relayCompose_window_exec_isPPT :
    Cslib.Probability.IsPPT encBool (fun κ z =>
      exec (compose relayHybrid windowProtocol) (dummyAdversary 2 _ _) ∅ relayEnv κ z) :=
  (isPPT_exec (WordPort.computable_partyIndex coinInputPort) windowProtocol_isPPT
    windowProtocol_isReplyBounded (Adversary.isPPT_dummyAdversary 2 _)
    (Machine.isReplyBounded_id _)
    (relayEnv_isPPT.absorbHybrid (WordPort.computable_partyIndex coinInputPort)
      relayHybrid_isPPT relayHybrid_isReplyBounded ∅) ∅).congr
    fun κ z => by rw [exec_compose_dummy]

/-- Observable, `κ`-dependent output of `compose relayHybrid windowProtocol` against `relayEnv`:
party `0` writes `[true ^^ c]` through `relayHybrid` to `windowProtocol`, and party `1` polls
`take κ [true ^^ c]`. -/
theorem relayCompose_window_exec_eval (κ : ℕ) (z : List Bool) :
    ProbComp.eval
        (exec (compose relayHybrid windowProtocol) (dummyAdversary 2 _ _) ∅ relayEnv κ z) =
      PMF.pure (decide (0 < κ)) := by
  rw [exec_compose_dummy]
  have hlink : absorbHybrid ∅ relayHybrid relayEnv = windowEnv := by
    funext κ' z'
    simp only [absorbHybrid, Machine.link, routeCorrupt, hybridWrap, liftParty,
      relayEnv, writePollEnv, relayHybrid, windowEnv, ProbOracleComp.sample_pure, pure_bind,
      Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure, StateT.run,
      Finset.notMem_empty, ↓reduceIte, OracleComp.interpret_bind,
      ProbOracleComp.interpret_query, OracleComp.interpret_pure, map_eq_bind_pure_comp,
      bind_assoc, Function.comp_apply]
  rw [hlink]
  exact windowExec_eval κ z

end CslibFrontierTests.Crypto.UCPPTExecution
