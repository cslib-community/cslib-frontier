/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Crypto.Protocols.UC.PPT
import CslibFrontier.Languages.Probabilistic.Oracle.Support
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Tests for `UC.PPT`

Non-degenerate witnesses for `CslibFrontier.Crypto.Protocols.UC.PPT`:

1. End-to-end witness with growing state, real coins, and state-dependent replies (`coinStore`):
   `coinStore : IdealFunctionality 2 Bool (List Bool) Unit Unit` appends a coin-masked bit on
   party-`0` writes and returns the full stored list on party-`1` polls. We certify
   `coinStore_isPPT`, lift it to `coinStore_toProtocol_isPPT` via
   `IdealFunctionality.IsPPT.toProtocol`, and certify `dummyAdversary_isPPT` via
   `Adversary.isPPT_dummyAdversary`.
2. Non-vacuity of `preserve` and state-dependent replies: a party-`0` write produces two distinct
   supported next states (real coins) whose encoded length strictly increases (so `growth = 0`
   fails), while a party-`1` poll returns a reply of length `s.length + 1` (unbounded in
   `(p, request)` alone, exercising why `PPTCertificate` imposes no state-independent reply bound).
3. Interactive environment witness (`coinEnv_isPPT`) making two party calls and one adversary call,
   composed end-to-end with `coinStore.toProtocol`'s `PPTCertificate` as `wordRun` via
   `Environment.IsPPT.isOraclePPTOn_run_wordHandle`, plus an observable execution witness
   (`coinStore_wordRun_delivers_coin`) showing the stored fair coin reaches `coinEnv` when
   `replyBound = 2` and truncates at `replyBound = 1`.
4. Machine-level witness that `PPTParam.replyBound` matters: on `dummyAdversary 2 Unit (List Bool)`
   against an oracle returning `[true, true, true]`, `replyBound = 2` truncates the word reply to
   `[true, true]`, `replyBound = 3` fits and returns `[true, true, true]`, and the two runs differ.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPPT

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

/-- Trivial polynomial-time decoder for `encUnit`. -/
@[expose] public def unitDecoder : Decoder encUnit where
  decode _ := ()
  decode_enc _ := rfl
  computable :=
    (ComputableInPolyTime.const (encIn := encBits) (encOut := encUnit) ()).exists_degree

/-- Trivial `Unit`/`Unit` word port. -/
@[expose] public def unitPort : WordPort Unit Unit where
  query := encUnit
  queryDecoder := unitDecoder
  reply := encUnit
  replyDecoder := unitDecoder

/-- Identity `List Bool` / `List Bool` word port. -/
@[expose] public def msgPort : WordPort (List Bool) (List Bool) where
  query := encBits
  queryDecoder := Decoder.bits
  reply := encBits
  replyDecoder := Decoder.bits

private def bitsPort : WordPort Unit (List Bool) where
  query := encUnit
  queryDecoder := unitDecoder
  reply := encBits
  replyDecoder := Decoder.bits

/-- Single-party `Bool`/`List Bool` word port for `coinStore`. -/
@[expose] public def coinInputPort : WordPort Bool (List Bool) where
  query := encBool
  queryDecoder := Decoder.bool
  reply := encBits
  replyDecoder := Decoder.bits

/-- Two-party indexed port for `coinStore`. -/
@[expose] public def coinPartyPort : WordPort (Fin 2 × Bool) (Option (List Bool)) :=
  WordPort.party (n := 2) coinInputPort

/-! ### 1. `coinStore` end-to-end witness -/

section CoinStoreWitness

/-- Two-party functionality with growing state and real coins: party `0` samples a fresh uniform
bit `c`, stores `(b ^^ c) :: s`, and returns `none`; party `1` polls and returns `some s`; the
backdoor is a no-op. -/
@[expose] public noncomputable def coinStore :
    IdealFunctionality 2 Bool (List Bool) Unit Unit where
  State := List Bool
  init _ _ := pure []
  onInput i b := do
    let s ← get
    if i = 0 then
      let c ← StateT.lift (ProbComp.uniform Bool)
      set ((b ^^ c) :: s)
      return none
    else
      return some s
  onBackdoor _ := return ()

private theorem coinStore_onInput_zero_eval (b : Bool) (s : List Bool) :
    ((coinStore.onInput (0 : Fin 2) b).run s).eval =
      PMF.map (fun c : Bool => ((none : Option (List Bool)), (b ^^ c) :: s))
        (ProbComp.uniform Bool).eval := by
  change (do
      let x ← (pure (s, s) : ProbComp _)
      let y ← ((fun c => (c, x.2)) <$> ProbComp.uniform Bool)
      let z ← (pure ((), (b ^^ y.1) :: x.1) : ProbComp _)
      pure ((none : Option (List Bool)), z.2)).eval =
    PMF.map (fun c : Bool => ((none : Option (List Bool)), (b ^^ c) :: s))
      (ProbComp.uniform Bool).eval
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, PMF.pure_bind,
    PMF.bind_map]
  rfl

public theorem coinStore_onInput_one_eval (b : Bool) (s : List Bool) :
    ((coinStore.onInput (1 : Fin 2) b).run s).eval =
      PMF.pure ((some s : Option (List Bool)), s) := by
  have hne : (1 : Fin 2) ≠ 0 := by decide
  change (do
      let x ← (pure (s, s) : ProbComp _)
      if (1 : Fin 2) = 0 then
        let y ← ((fun c => (c, x.2)) <$> ProbComp.uniform Bool)
        let z ← (pure ((), (b ^^ y.1) :: x.1) : ProbComp _)
        pure ((none : Option (List Bool)), z.2)
      else
        pure ((some x.1 : Option (List Bool)), x.2)).eval =
    PMF.pure ((some s : Option (List Bool)), s)
  simp only [hne, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]

private theorem coinStore_onBackdoor_eval (u : Unit) (s : List Bool) :
    ((coinStore.onBackdoor u).run s).eval = PMF.pure ((), s) := by
  change (pure ((), s) : ProbComp _).eval = PMF.pure ((), s)
  exact ProbComp.eval_pure ((), s)

private theorem coinStore_onInput_zero_support (b : Bool) (s : coinStore.State)
    (r : Option (List Bool) × coinStore.State) :
    r ∈ ((coinStore.onInput (0 : Fin 2) b).run s).eval.support ↔
      ∃ c : Bool, r.1 = none ∧ (r.2 : List Bool) = (b ^^ c) :: (s : List Bool) := by
  let sBits : List Bool := s
  let rBits : Option (List Bool) × List Bool := (r.1, r.2)
  have h : ((coinStore.onInput (0 : Fin 2) b).run s).eval r =
      (PMF.map (fun c : Bool => ((none : Option (List Bool)), (b ^^ c) :: sBits))
        (ProbComp.uniform Bool).eval) rBits :=
    congrFun (congrArg DFunLike.coe (coinStore_onInput_zero_eval b sBits)) rBits
  rw [PMF.mem_support_iff, h, ← PMF.mem_support_iff, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨c, (congrArg Prod.fst hc).symm, (congrArg Prod.snd hc).symm⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, by simp [ProbComp.eval_uniform], Prod.ext h1.symm h2.symm⟩

private theorem coinStore_onInput_one_support (b : Bool) (s : coinStore.State)
    (r : Option (List Bool) × coinStore.State) :
    r ∈ ((coinStore.onInput (1 : Fin 2) b).run s).eval.support ↔
      r.1 = some (s : List Bool) ∧ (r.2 : List Bool) = (s : List Bool) := by
  let sBits : List Bool := s
  let rBits : Option (List Bool) × List Bool := (r.1, r.2)
  have h : ((coinStore.onInput (1 : Fin 2) b).run s).eval r =
      (PMF.pure ((some sBits : Option (List Bool)), sBits)) rBits :=
    congrFun (congrArg DFunLike.coe (coinStore_onInput_one_eval b sBits)) rBits
  rw [PMF.mem_support_iff, h, ← PMF.mem_support_iff, PMF.mem_support_pure_iff]
  exact Prod.ext_iff

private theorem coinStore_onBackdoor_support (u : Unit) (s : coinStore.State)
    (r : Unit × coinStore.State) :
    r ∈ ((coinStore.onBackdoor u).run s).eval.support ↔
      r.1 = () ∧ (r.2 : List Bool) = (s : List Bool) := by
  let sBits : List Bool := s
  let rBits : Unit × List Bool := (r.1, r.2)
  have h : ((coinStore.onBackdoor u).run s).eval r = (PMF.pure ((), sBits)) rBits :=
    congrFun (congrArg DFunLike.coe (coinStore_onBackdoor_eval u sBits)) rBits
  rw [PMF.mem_support_iff, h, ← PMF.mem_support_iff, PMF.mem_support_pure_iff]
  exact Prod.ext_iff

/-- Identity `List Bool` state codec. -/
@[expose] public def bitsWordCodec : WordCodec (List Bool) where
  enc := encBits
  decode := id
  decode_enc _ := rfl

/-- Party-`0` coin-masked write step shared by `coinStore` and `windowProtocol`. -/
public theorem isPPTOn_coinWriteStep :
    IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
      (fun p =>
        (fun c => (coinPartyPort.reply none,
          ((coinPartyPort.queryDecoder.decode p.1).2 ^^ c) :: p.2)) <$> ProbComp.uniform Bool) := by
  have hbit : ComputableInPolyTime
      (fun p : List Bool × List Bool => (coinPartyPort.queryDecoder.decode p.1).2)
      (encPair encBits encBits) encBool :=
    (ComputableInPolyTime.snd (encFinEnum (Fin 2)) encBool).comp
      (coinPartyPort.queryDecoder.computableInPolyTime.comp
        (ComputableInPolyTime.fst encBits encBits))
  refine (isPPTOn_uniform_bool (encPair encBits encBits)).map_with ?_
  have hfst : ComputableInPolyTime
      (fun _ : (List Bool × List Bool) × Bool => coinPartyPort.reply none)
      (encPair (encPair encBits encBits) encBool) encBits :=
    ComputableInPolyTime.const (coinPartyPort.reply none)
  have hxor : ComputableInPolyTime
      (fun x : (List Bool × List Bool) × Bool =>
        (coinPartyPort.queryDecoder.decode x.1.1).2 ^^ x.2)
      (encPair (encPair encBits encBits) encBool) encBool :=
    ComputableInPolyTime.bool_xor.comp
      ((hbit.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  have hhead : ComputableInPolyTime
      (fun x : (List Bool × List Bool) × Bool =>
        [(coinPartyPort.queryDecoder.decode x.1.1).2 ^^ x.2])
      (encPair (encPair encBits encBits) encBool) encBits :=
    (ComputableInPolyTime.of_finite (fun b : Bool => [b]) (encIn := encBool)
      (encOut := encBits)).comp hxor
  have htail : ComputableInPolyTime
      (fun x : (List Bool × List Bool) × Bool => x.1.2)
      (encPair (encPair encBits encBits) encBool) encBits := by
    fun_prop
  have hsnd : ComputableInPolyTime
      (fun x : (List Bool × List Bool) × Bool =>
        ((coinPartyPort.queryDecoder.decode x.1.1).2 ^^ x.2) :: x.1.2)
      (encPair (encPair encBits encBits) encBool) encBits :=
    ComputableInPolyTime.bitsAppend hhead htail
  exact hfst.prod hsnd

private theorem coinStore_onInput_isPPTOn :
    IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
      (IdealFunctionality.wordStep coinPartyPort bitsWordCodec
        fun q => coinStore.onInput q.1 q.2) := by
  have hcond : ComputableInPolyTime
      (fun p : List Bool × List Bool => decide ((coinPartyPort.queryDecoder.decode p.1).1 = 0))
      (encPair encBits encBits) encBool := by
    have hfin : ComputableInPolyTime (fun i : Fin 2 => decide (i = 0))
        (encFinite (Fin 2)) encBool :=
      ComputableInPolyTime.of_finite (fun i : Fin 2 => decide (i = 0))
    exact hfin.comp ((WordPort.computable_partyIndex coinInputPort).comp
      (ComputableInPolyTime.fst encBits encBits))
  have hno : IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
      (fun p => pure (coinPartyPort.reply (some p.2), p.2)) := by
    have hrep : ComputableInPolyTime
        (fun p : List Bool × List Bool => coinPartyPort.reply (some p.2))
        (encPair encBits encBits) encBits := by
      have hsome : ComputableInPolyTime
          (fun p : List Bool × List Bool => some p.2)
          (encPair encBits encBits) (encOption encBits) := by
        fun_prop
      exact (ComputableInPolyTime.of_eq (encIn := encOption encBits) (encOut := encBits)
        (f := coinPartyPort.reply) (fun _ => rfl)).comp hsome
    have hstate : ComputableInPolyTime (fun p : List Bool × List Bool => p.2)
        (encPair encBits encBits) encBits := by
      fun_prop
    exact (hrep.prod hstate).isPPTOn
  refine (IsPPTOn.ite (condition := fun p => (coinPartyPort.queryDecoder.decode p.1).1 = 0)
    hcond isPPTOn_coinWriteStep hno).congr fun p => ?_
  dsimp only [IdealFunctionality.wordStep]
  by_cases hi : (coinPartyPort.queryDecoder.decode p.1).1 = 0
  · simp only [hi, ↓reduceIte, ProbComp.eval_map]
    change _ = PMF.map (fun result : Option (List Bool) × List Bool =>
      (coinPartyPort.reply result.1, encBits result.2))
      ((coinStore.onInput 0 (coinPartyPort.queryDecoder.decode p.1).2).run p.2).eval
    rw [coinStore_onInput_zero_eval]
    rw [PMF.map_comp]
    rfl
  · have hi1 : (coinPartyPort.queryDecoder.decode p.1).1 = 1 := by omega
    simp only [hi, ↓reduceIte, ProbComp.eval_pure, ProbComp.eval_map]
    rw [hi1]
    change _ = PMF.map (fun result : Option (List Bool) × List Bool =>
      (coinPartyPort.reply result.1, encBits result.2))
      ((coinStore.onInput 1 (coinPartyPort.queryDecoder.decode p.1).2).run p.2).eval
    rw [coinStore_onInput_one_eval]
    rw [PMF.pure_map]
    rfl

private noncomputable def coinStoreCert :
    IdealFunctionality.PPTCertificate coinStore coinPartyPort unitPort where
  stateCodec := bitsWordCodec
  init := by
    change IsPPTOn (encPair encUnary (encFinite (Finset (Fin 2)))) encBits (fun _ => pure [])
    exact (ComputableInPolyTime.const []).isPPTOn
  onInput := coinStore_onInput_isPPTOn
  onBackdoor := by
    have hf : ComputableInPolyTime
        (fun p : List Bool × List Bool => (unitPort.reply (), p.2))
        (encPair encBits encBits) (encPair encBits encBits) := by
      fun_prop
    exact hf.isPPTOn.congr fun p => by
      simp only [IdealFunctionality.wordStep, ProbComp.eval_pure, ProbComp.eval_map]
      change _ = PMF.map (fun result : Unit × List Bool =>
        (unitPort.reply result.1, encBits result.2))
        ((coinStore.onBackdoor (unitPort.queryDecoder.decode p.1)).run p.2).eval
      rw [coinStore_onBackdoor_eval, PMF.pure_map]
      rfl
  normalize := ComputableInPolyTime.id'
  growth _ := 1
  growth_poly := PolyBounded.const 1
  preserve_onInput req s result hr := by
    by_cases hi : (coinPartyPort.queryDecoder.decode req).1 = 0
    · rw [hi, coinStore_onInput_zero_support] at hr
      rcases hr with ⟨c, _, hs⟩
      have hlen : (result.2 : List Bool).length = (s : List Bool).length + 1 :=
        (congrArg List.length hs).trans List.length_cons
      change (result.2 : List Bool).length ≤ (s : List Bool).length + 1
      omega
    · have hi1 : (coinPartyPort.queryDecoder.decode req).1 = 1 := by omega
      rw [hi1, coinStore_onInput_one_support] at hr
      change (result.2 : List Bool).length ≤ (s : List Bool).length + 1
      rw [hr.2]
      omega
  preserve_onBackdoor req s result hr := by
    rw [coinStore_onBackdoor_support] at hr
    change (result.2 : List Bool).length ≤ (s : List Bool).length + 1
    rw [hr.2]
    omega

/-- `coinStore` is a strict-PPT ideal functionality. -/
public theorem coinStore_isPPT : coinStore.IsPPT coinPartyPort unitPort :=
  ⟨coinStoreCert⟩

/-- Lifting `coinStore` via `IdealFunctionality.IsPPT.toProtocol` yields a strict-PPT protocol. -/
public theorem coinStore_toProtocol_isPPT : coinStore.toProtocol.IsPPT coinPartyPort unitPort :=
  coinStore_isPPT.toProtocol

/-- The dummy adversary forwarding `Unit / Unit` is strict PPT. -/
theorem dummyAdversary_isPPT : (dummyAdversary 2 Unit Unit).IsPPT unitPort unitPort :=
  Adversary.isPPT_dummyAdversary 2 unitPort

/-! ### 2. Non-vacuity: real coins, strict state growth, and state-dependent replies -/

private def coinStoreCodec : StateCodec coinStore.toProtocol := fun _ _ => bitsWordCodec

/-- A party-`0` store activation from `[false, true]` has two distinct supported next states
`[true, false, true]` and `[false, false, true]` (real coins), both strictly longer than the
input state (`3 > 2`), showing `growth = 0` cannot satisfy `PPTCertificate.preserve`. -/
theorem coinStore_state_grows_two_outcomes :
    let p : PPTParam 2 := ⟨1, 4, ∅⟩
    let req := (Sum.inl (), coinPartyPort.query ((0 : Fin 2), true))
    let s : List Bool := [false, true]
    (coinPartyPort.reply none, [true, false, true]) ∈
      OracleComp.support (wordHandle coinStore.toProtocol WordInterface.empty
        (WordInterface.protocol coinPartyPort unitPort) coinStoreCodec p req s) ∧
    (coinPartyPort.reply none, [false, false, true]) ∈
      OracleComp.support (wordHandle coinStore.toProtocol WordInterface.empty
        (WordInterface.protocol coinPartyPort unitPort) coinStoreCodec p req s) := by
  have hmem : ∀ c : Bool,
      (coinPartyPort.reply none, (true ^^ c) :: [false, true]) ∈
        OracleComp.support (wordHandle coinStore.toProtocol WordInterface.empty
          (WordInterface.protocol coinPartyPort unitPort) coinStoreCodec ⟨1, 4, ∅⟩
          (Sum.inl (), coinPartyPort.query ((0 : Fin 2), true)) [false, true]) := by
    intro c
    have hdec : coinPartyPort.queryDecoder.1 (coinPartyPort.query ((0 : Fin 2), true)) =
        ((0 : Fin 2), true) := coinPartyPort.queryDecoder.decode_enc ((0 : Fin 2), true)
    have hsupp : ((none : Option (List Bool)), ((true ^^ c) :: [false, true] : coinStore.State)) ∈
        ((coinStore.onInput (0 : Fin 2) true).run ([false, true] : coinStore.State)).eval.support :=
      (coinStore_onInput_zero_support true [false, true] _).2 ⟨c, rfl, rfl⟩
    simp only [wordHandle, IdealFunctionality.toProtocol, WordInterface.protocol,
      WordInterface.sum, WordInterface.net, StateT.run, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_sample, OracleComp.mem_supportWith_map_iff]
    refine ⟨(none, ((true ^^ c) :: [false, true] : coinStore.State)), ?_, rfl⟩
    change _ ∈ OracleComp.support (ProbOracleComp.sample _)
    rw [ProbOracleComp.support_sample, hdec]
    exact hsupp
  exact ⟨hmem false, hmem true⟩

/-- A party-`1` poll activation returns a reply encoding `some s` of length `s.length + 1`,
unbounded in `(p, request)` alone: no state-independent reply bound certifies `coinStore`. -/
theorem coinStore_reply_grows_with_state (s : List Bool) :
    let p : PPTParam 2 := ⟨1, 4, ∅⟩
    let req := (Sum.inl (), coinPartyPort.query ((1 : Fin 2), false))
    (coinPartyPort.reply (some s), s) ∈
      OracleComp.support (wordHandle coinStore.toProtocol WordInterface.empty
        (WordInterface.protocol coinPartyPort unitPort) coinStoreCodec p req s) ∧
    (coinPartyPort.reply (some s)).length = s.length + 1 := by
  refine ⟨?_, ?_⟩
  · have hdec : coinPartyPort.queryDecoder.1 (coinPartyPort.query ((1 : Fin 2), false)) =
        ((1 : Fin 2), false) := coinPartyPort.queryDecoder.decode_enc ((1 : Fin 2), false)
    have hsupp : ((some s : Option (List Bool)), (s : coinStore.State)) ∈
        ((coinStore.onInput (1 : Fin 2) false).run (s : coinStore.State)).eval.support :=
      (coinStore_onInput_one_support false s _).2 ⟨rfl, rfl⟩
    simp only [wordHandle, IdealFunctionality.toProtocol, WordInterface.protocol,
      WordInterface.sum, WordInterface.net, StateT.run, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_sample, OracleComp.mem_supportWith_map_iff]
    refine ⟨(some s, (s : coinStore.State)), ?_, rfl⟩
    change _ ∈ OracleComp.support (ProbOracleComp.sample _)
    rw [ProbOracleComp.support_sample, hdec]
    exact hsupp
  · simp [coinPartyPort, WordPort.party, coinInputPort, encOption_some, encBits_apply]

/-! ### 3. Interactive environment witness and `SubstitutionGrowth` integration -/

/-- Environment making two party calls (store `true` at party `0`, poll at party `1`) and one
adversary call, outputting the head bit of the polled list (or `false`). -/
private def coinEnv : Environment 2 Bool (List Bool) Unit Unit :=
  fun _ _ => do
    let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), true))
    let polled ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), false))
    let _ ← ProbOracleComp.query (Sum.inr ())
    return match polled with
      | some (b :: _) => b
      | _ => false

private noncomputable def coinExec :=
  WordInterface.exec coinPartyPort unitPort

private noncomputable def coinConstQuery (q : (Fin 2 × Bool) ⊕ Unit) (e : EnvParam) :
    WordOracleComp coinExec.Channel (List Bool) :=
  coinExec.reply q <$>
    ProbOracleComp.lowerWith coinExec e.replyBound (ProbOracleComp.query q)

private theorem isOraclePPTOn_coinConstQuery (q : (Fin 2 × Bool) ⊕ Unit) :
    IsOraclePPTOn encEnvParam encBits (coinConstQuery q) :=
  coinExec.isOraclePPTOn_lowerWith_query
    (query := fun _ : EnvParam => q)
    (limit := fun e => e.replyBound)
    (ComputableInPolyTime.const _)
    (ComputableInPolyTime.const _)
    (by fun_prop)

/-- `coinEnv` is uniform strict oracle PPT (`Environment.IsPPT`). -/
theorem coinEnv_isPPT : coinEnv.IsPPT coinPartyPort unitPort := by
  let q1 := coinConstQuery (Sum.inl ((0 : Fin 2), true))
  let q2 : EnvParam → List Bool → WordOracleComp coinExec.Channel (List Bool) :=
    fun e _ => coinConstQuery (Sum.inl ((1 : Fin 2), false)) e
  let q3 : EnvParam → List Bool → WordOracleComp coinExec.Channel (List Bool) :=
    fun e _ => coinConstQuery (Sum.inr ()) e
  have hq1 : IsOraclePPTOn encEnvParam encBits q1 := isOraclePPTOn_coinConstQuery _
  have hq2 : IsOraclePPTOn (encPair encEnvParam encBits) encBits (fun x => q2 x.1 x.2) :=
    (isOraclePPTOn_coinConstQuery _).preprocess (ComputableInPolyTime.fst encEnvParam encBits)
  have hq3 : IsOraclePPTOn (encPair encEnvParam encBits) encBits (fun x => q3 x.1 x.2) :=
    (isOraclePPTOn_coinConstQuery _).preprocess (ComputableInPolyTime.fst encEnvParam encBits)
  have h12 : IsOraclePPTOn encEnvParam encBits (fun e => q1 e >>= q2 e) :=
    hq1.bind_with (second := q2) hq2
  have hpost : ComputableInPolyTime
      (fun pair : (EnvParam × List Bool) × List Bool =>
        match coinPartyPort.replyDecoder.decode pair.1.2 with
        | some (b :: _) => b
        | _ => false)
      (encPair (encPair encEnvParam encBits) encBits) encBool := by
    have hproj : ComputableInPolyTime
        (fun pair : (EnvParam × List Bool) × List Bool => pair.1.2)
        (encPair (encPair encEnvParam encBits) encBits) encBits :=
      (ComputableInPolyTime.snd encEnvParam encBits).comp
        (ComputableInPolyTime.fst (encPair encEnvParam encBits) encBits)
    have hdec : ComputableInPolyTime
        (fun pair : (EnvParam × List Bool) × List Bool =>
          coinPartyPort.replyDecoder.decode pair.1.2)
        (encPair (encPair encEnvParam encBits) encBits) (encOption encBits) :=
      coinPartyPort.replyDecoder.computableInPolyTime.comp hproj
    have hlist : ComputableInPolyTime
        (fun pair : (EnvParam × List Bool) × List Bool =>
          (coinPartyPort.replyDecoder.decode pair.1.2).getD [])
        (encPair (encPair encEnvParam encBits) encBits) encBits :=
      (ComputableInPolyTime.optionGetD encBits).comp
        (hdec.prod (ComputableInPolyTime.const []))
    have hhead : ComputableInPolyTime
        (fun pair : (EnvParam × List Bool) × List Bool =>
          ((coinPartyPort.replyDecoder.decode pair.1.2).getD []).getD 0 false)
        (encPair (encPair encEnvParam encBits) encBits) encBool :=
      ComputableInPolyTime.bitsGetDWithInput hlist (ComputableInPolyTime.const 0) false
    have heq : (fun pair : (EnvParam × List Bool) × List Bool =>
        ((coinPartyPort.replyDecoder.decode pair.1.2).getD []).getD 0 false) =
      (fun pair : (EnvParam × List Bool) × List Bool =>
        match coinPartyPort.replyDecoder.decode pair.1.2 with
        | some (b :: _) => b
        | _ => false) := by
      funext pair
      cases coinPartyPort.replyDecoder.decode pair.1.2 with
      | none => rfl
      | some l => cases l <;> rfl
    exact heq ▸ hhead
  have h3out : IsOraclePPTOn (encPair encEnvParam encBits) encBool fun x =>
      (fun _ => match coinPartyPort.replyDecoder.decode x.2 with
        | some (b :: _) => b
        | _ => false) <$> q3 x.1 x.2 := by
    refine (hq3.keep_input.map hpost).congr fun x State oracle s => ?_
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    rfl
  have h123 : IsOraclePPTOn encEnvParam encBool fun e =>
      (q1 e >>= q2 e) >>= fun w =>
        (fun _ => match coinPartyPort.replyDecoder.decode w with
          | some (b :: _) => b
          | _ => false) <$> q3 e w :=
    h12.bind_with h3out
  refine h123.congr fun e State oracle s => ?_
  have hdec : ∀ r : Option (List Bool),
      coinPartyPort.replyDecoder.decode
        (coinExec.reply (Sum.inl ((1 : Fin 2), false)) r) = r :=
    fun r => coinPartyPort.replyDecoder.decode_enc r
  simp only [q1, q2, q3, coinConstQuery, coinEnv, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pure, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp_apply, hdec]
  rfl

/-- Direct end-to-end instantiation of `Environment.IsPPT.isOraclePPTOn_run_wordHandle`:
`wordRun` executing `coinEnv` against `coinStore.toProtocol` is uniform strict oracle PPT. -/
theorem coinEnv_run_coinStore_wordHandle_isOraclePPTOn :
    ∃ cert : PPTCertificate coinStore.toProtocol WordInterface.empty
      (WordInterface.protocol coinPartyPort unitPort),
      IsOraclePPTOn (Operation := WordInterface.empty.Channel) encEnvParam encBool
        (wordRun coinStore.toProtocol WordInterface.empty coinPartyPort unitPort
          cert.codec coinEnv (fun e => ⟨e.secParam, e.replyBound, ∅⟩) id) := by
  rcases coinStore_toProtocol_isPPT with ⟨cert⟩
  have hconst : ComputableInPolyTime (fun _ : EnvParam => (∅ : Finset (Fin 2)))
      encEnvParam (encFinite (Finset (Fin 2))) :=
    ComputableInPolyTime.const ∅
  exact ⟨cert, coinEnv_isPPT.isOraclePPTOn_run_wordHandle cert (by fun_prop)
    (ComputableInPolyTime.of_eq fun _ => rfl)⟩

/-- Empty word oracle on `WordInterface.empty`. -/
@[expose] public noncomputable def emptyWordOracle :
    WordInterface.empty.Channel × List Bool → StateT Unit PMF (List Bool)
  | cw, _ => cw.1.elim

private theorem runWith_lowerWith_empty_sample {α : Type} (k : ℕ) (p : ProbComp α) :
    ProbOracleComp.runWith emptyWordOracle
        (ProbOracleComp.lowerWith WordInterface.empty k (ProbOracleComp.sample p)) () =
      p.eval.map (·, ()) := by
  rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_sample, ProbOracleComp.runWith_sample]

/-- Observable `wordRun` witness: for any `PPTCertificate` of `coinStore.toProtocol`, running
`coinEnv` through `wordRun` with fitting `replyBound = 2` delivers the fair stored coin to the
environment (`PMF` probability `1 / 2` on `true`), whereas truncating at `replyBound = 1` drops the
stored bit and forces `false` (probability `0` on `true`). -/
theorem coinStore_wordRun_delivers_coin
    (cert : PPTCertificate coinStore.toProtocol WordInterface.empty
      (WordInterface.protocol coinPartyPort unitPort))
    (κ : ℕ) (z : List Bool) :
    ProbOracleComp.runWith emptyWordOracle
      (wordRun coinStore.toProtocol WordInterface.empty coinPartyPort unitPort
        cert.codec coinEnv (fun e => ⟨e.secParam, e.replyBound, ∅⟩) id ⟨κ, 2, z⟩) () (true, ()) =
      (1 / 2 : ENNReal) ∧
    ProbOracleComp.runWith emptyWordOracle
      (wordRun coinStore.toProtocol WordInterface.empty coinPartyPort unitPort
        cert.codec coinEnv (fun e => ⟨e.secParam, e.replyBound, ∅⟩) id ⟨κ, 1, z⟩) () (true, ()) =
      0 := by
  have hrun (k : ℕ) :
      ProbOracleComp.runWith emptyWordOracle
        (wordRun coinStore.toProtocol WordInterface.empty coinPartyPort unitPort
          cert.codec coinEnv (fun e => ⟨e.secParam, e.replyBound, ∅⟩) id ⟨κ, k, z⟩) () =
        (ProbComp.uniform Bool).eval.map (fun c =>
          (match coinPartyPort.replyDecoder.decode
              (List.take k (coinPartyPort.reply (some [true ^^ c]))) with
          | some (b :: _) => b
          | _ => false, ())) := by
    have hproto0 (s : (coinStore.toProtocol κ ∅).State) :
        ProbOracleComp.runWith emptyWordOracle
          (ProbOracleComp.lowerWith WordInterface.empty k
            ((coinStore.toProtocol κ ∅).handle
              (Sum.inl (coinPartyPort.queryDecoder.decode
                (coinPartyPort.query ((0 : Fin 2), true))))
              s)) () =
          PMF.map (fun c : Bool =>
              (((none : Option (List Bool)),
                (((true ^^ c) :: (s : List Bool)) : (coinStore.toProtocol κ ∅).State)), ()))
            (ProbComp.uniform Bool).eval := by
      let s' : List Bool := s
      let q0 := coinPartyPort.queryDecoder.decode (coinPartyPort.query ((0 : Fin 2), true))
      have hq0 : q0 = ((0 : Fin 2), true) := coinPartyPort.queryDecoder.decode_enc _
      change ProbOracleComp.runWith emptyWordOracle
          (ProbOracleComp.lowerWith WordInterface.empty k
            (ProbOracleComp.sample ((coinStore.onInput q0.1 q0.2).run s'))) () = _
      rw [hq0, runWith_lowerWith_empty_sample]
      dsimp only
      rw [coinStore_onInput_zero_eval]
      refine Eq.trans (PMF.map_comp
        (fun c : Bool => ((none : Option (List Bool)), (true ^^ c) :: s'))
        (ProbComp.uniform Bool).eval (fun x => (x, ()))) ?_
      rfl
    have hproto1 (s : (coinStore.toProtocol κ ∅).State) :
        ProbOracleComp.runWith emptyWordOracle
          (ProbOracleComp.lowerWith WordInterface.empty k
            ((coinStore.toProtocol κ ∅).handle
              (Sum.inl (coinPartyPort.queryDecoder.decode
                (coinPartyPort.query ((1 : Fin 2), false))))
              s)) () =
          PMF.pure (((some (s : List Bool) : Option (List Bool)), s), ()) := by
      let s' : List Bool := s
      let q1 := coinPartyPort.queryDecoder.decode (coinPartyPort.query ((1 : Fin 2), false))
      have hq1 : q1 = ((1 : Fin 2), false) := coinPartyPort.queryDecoder.decode_enc _
      change ProbOracleComp.runWith emptyWordOracle
          (ProbOracleComp.lowerWith WordInterface.empty k
            (ProbOracleComp.sample ((coinStore.onInput q1.1 q1.2).run s'))) () = _
      rw [hq1, runWith_lowerWith_empty_sample, coinStore_onInput_one_eval]
      exact PMF.pure_map (fun x : Option (List Bool) × List Bool => (x, ())) (some s', s')
    have hprotoU (s : (coinStore.toProtocol κ ∅).State) :
        ProbOracleComp.runWith emptyWordOracle
          (ProbOracleComp.lowerWith WordInterface.empty k
            ((coinStore.toProtocol κ ∅).handle (Sum.inr ()) s)) () =
          PMF.pure (((), s), ()) := by
      let s' : List Bool := s
      change ProbOracleComp.runWith emptyWordOracle
          (ProbOracleComp.lowerWith WordInterface.empty k
            (ProbOracleComp.sample ((coinStore.onBackdoor ()).run s'))) () = _
      rw [runWith_lowerWith_empty_sample, coinStore_onBackdoor_eval]
      exact PMF.pure_map (fun x : Unit × List Bool => (x, ())) ((), s')
    let sInit : (coinStore.toProtocol κ ∅).State := ([] : List Bool)
    have hinit : (coinStore.toProtocol κ ∅).init = pure sInit := rfl
    simp only [wordRun, hinit, map_pure, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_sample, ProbOracleComp.runWith_map, ProbComp.eval_pure, PMF.pure_map,
      PMF.pure_bind]
    simp only [wordRunFrom, coinEnv, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
      ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_map, ProbOracleComp.interpret_query,
      OracleComp.interpret_pure, StateT.run_bind, StateT.run_map, StateT.run_pure]
    simp only [wordHandle, StateT.run, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_pure]
    dsimp only [WordInterface.exec, WordInterface.sum, WordInterface.net, Sum.map, Sum.elim,
      Function.comp_apply]
    simp only [(cert.codec κ ∅).decode_enc, hproto0, hproto1, hprotoU]
    simp only [PMF.bind_map, PMF.map_bind, PMF.pure_bind, PMF.pure_map,
      Prod.map, Function.comp_def, id_eq, (cert.codec κ ∅).decode_enc]
    change ((PMF.map (Prod.map
        (fun result : Option (List Bool) × (coinStore.toProtocol κ ∅).State =>
          (coinPartyPort.reply result.1, (cert.codec κ ∅).enc result.2)) id)
        (PMF.map (fun c : Bool =>
          (((none : Option (List Bool)),
            ((true ^^ c) :: (sInit : List Bool) : (coinStore.toProtocol κ ∅).State)), ()))
          (ProbComp.uniform Bool).eval)).bind fun a =>
      PMF.pure
        (match coinPartyPort.replyDecoder.decode
            (List.take k (coinPartyPort.reply (some ((cert.codec κ ∅).decode a.1.2)))) with
        | some (b :: _) => b
        | _ => false, ())) = _
    rw [PMF.bind_map, PMF.bind_map]
    simp only [Function.comp_def, Prod.map, id_eq, (cert.codec κ ∅).decode_enc, sInit]
    exact PMF.bind_pure_comp _ _
  refine ⟨?_, ?_⟩
  · rw [hrun 2]
    have hfit : ∀ x : Bool,
        coinPartyPort.replyDecoder.decode
          (List.take 2 (coinPartyPort.reply (some [x]))) = some [x] := by
      intro x
      have hlen : (coinPartyPort.reply (some [x])).length = 2 := by
        simp [coinPartyPort, WordPort.party, coinInputPort, encOption_some, encBits_apply]
      rw [List.take_of_length_le (by omega), coinPartyPort.replyDecoder.decode_enc]
    simp only [hfit, Bool.true_xor, PMF.map_apply, ProbComp.eval_uniform,
      PMF.uniformOfFintype_apply, Fintype.card_bool]
    have hsum : (∑ x : Bool, if (true, ()) = (!x, ()) then (2⁻¹ : ENNReal) else 0) =
        (2⁻¹ : ENNReal) := by
      rw [Fintype.sum_bool]
      simp
    simp [one_div]
  · rw [hrun 1]
    have htrunc : ∀ x : Bool,
        coinPartyPort.replyDecoder.decode
          (List.take 1 (coinPartyPort.reply (some [x]))) = some [] := by
      intro x
      cases x <;> rfl
    simp only [htrunc, PMF.map_apply]
    simp

end CoinStoreWitness

/-! ### 4. `PPTParam.replyBound` matters at machine level -/

section ReplyBoundWitness

private noncomputable def tripleOracle : (q : Unit) → StateT Unit PMF (List Bool)
  | (), s => PMF.pure ([true, true, true], s)

/-- Machine-level witness that `PPTParam.replyBound` changes the lowered activation of
`dummyAdversary 2 Unit (List Bool)`: for any `PPTCertificate` of the dummy adversary, running
`wordHandle` against `tripleOracle` truncates to `[true, true]` at `replyBound = 2`, fits and
returns `[true, true, true]` at `replyBound = 3`, and the two distributions differ. -/
theorem dummyAdversary_wordHandle_replyBound_truncates_and_fits
    (cert : PPTCertificate (dummyAdversary 2 Unit (List Bool))
      (WordInterface.net bitsPort) (WordInterface.net bitsPort)) :
      let pTrunc : PPTParam 2 := ⟨1, 2, ∅⟩
      let pFit : PPTParam 2 := ⟨1, 3, ∅⟩
      let state0 := (cert.codec 1 ∅).enc PUnit.unit
      ProbOracleComp.runWith ((WordInterface.net bitsPort).encodeOracle tripleOracle)
        (wordHandle (dummyAdversary 2 Unit (List Bool))
          (WordInterface.net bitsPort) (WordInterface.net bitsPort)
          cert.codec pTrunc ((), []) state0) () =
        PMF.pure (([true, true], state0), ()) ∧
      ProbOracleComp.runWith ((WordInterface.net bitsPort).encodeOracle tripleOracle)
        (wordHandle (dummyAdversary 2 Unit (List Bool))
          (WordInterface.net bitsPort) (WordInterface.net bitsPort)
          cert.codec pFit ((), []) state0) () =
        PMF.pure (([true, true, true], state0), ()) ∧
      ProbOracleComp.runWith ((WordInterface.net bitsPort).encodeOracle tripleOracle)
        (wordHandle (dummyAdversary 2 Unit (List Bool))
          (WordInterface.net bitsPort) (WordInterface.net bitsPort)
          cert.codec pTrunc ((), []) state0) () ≠
      ProbOracleComp.runWith ((WordInterface.net bitsPort).encodeOracle tripleOracle)
        (wordHandle (dummyAdversary 2 Unit (List Bool))
          (WordInterface.net bitsPort) (WordInterface.net bitsPort)
          cert.codec pFit ((), []) state0) () := by
  have hrun : ∀ k : ℕ,
      ProbOracleComp.runWith ((WordInterface.net bitsPort).encodeOracle tripleOracle)
        (wordHandle (dummyAdversary 2 Unit (List Bool))
          (WordInterface.net bitsPort) (WordInterface.net bitsPort)
          cert.codec ⟨1, k, ∅⟩ ((), []) ((cert.codec 1 ∅).enc PUnit.unit)) () =
        PMF.pure ((List.take k [true, true, true], (cert.codec 1 ∅).enc PUnit.unit), ()) := by
    intro k
    simp only [wordHandle, dummyAdversary, Machine.id, StateT.run, StateT.lift,
      ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pure,
      ProbOracleComp.simulate_query, WordInterface.lowerQuery, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
      WordInterface.encodeOracle_apply]
    simp only [WordInterface.net, bitsPort, tripleOracle, Decoder.bits, encBits_apply,
      PMF.pure_bind, PMF.pure_map, id_eq]
    exact congrArg
      (fun u => PMF.pure ((List.take k [true, true, true], (cert.codec 1 ∅).enc u), ()))
      ((cert.codec 1 ∅).decode_enc PUnit.unit)
  refine ⟨hrun 2, hrun 3, ?_⟩
  rw [hrun 2, hrun 3]
  intro h
  have hv := congrArg (fun p => p (([true, true], (cert.codec 1 ∅).enc PUnit.unit), ())) h
  simp at hv

end ReplyBoundWitness

end CslibFrontierTests.Crypto.UCPPT
