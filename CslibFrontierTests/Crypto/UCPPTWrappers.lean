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
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Protocols.UC.Execution
import CslibFrontier.Crypto.Protocols.UC.PPT
import CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers
import CslibFrontier.Languages.Probabilistic.Oracle.Support

/-!
# Tests for `UC.PPT.Wrappers`

Non-degenerate witnesses for `CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers`:

1. `windowStore`: a two-party functionality storing `(κ, log)`, where party-`0` writes mask a bit
   with a uniform coin and grow the log without bound, and party-`1` polls return the most recent
   `κ` bits (`s.take κ`). Certified via `IdealFunctionality.IsPPT` (including `normalize`) and
   lifted via `toProtocol`.
2. `corruptRouter`: routing branches matter on `corruptRouter {1} (windowStore.toProtocol κ {1})`
   (environment inputs to corrupted party `1` drop without touching state; adversary-routed inputs
   to party `1` and honest party `0` inputs reach `windowStore`), certified via
   `Protocol.IsPPT.corruptRouter` and `WordPort.computable_partyIndex`.
3. `logAdv` and `liftAdversary`: a stateful unary-counter adversary forwarding `List Bool` queries
   is certified, lifted via `Adversary.IsPPT.liftAdversary`, and checked to forward left-channel
   party queries while normalizing the state word.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPPTWrappers

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

private def unitDecoder : Decoder encUnit where
  decode _ := ()
  decode_enc _ := rfl
  computable :=
    (ComputableInPolyTime.const (encIn := encBits) (encOut := encUnit) ()).exists_degree

private def unitPort : WordPort Unit Unit :=
  ⟨encUnit, unitDecoder, encUnit, unitDecoder⟩

private def windowInputPort : WordPort Bool (List Bool) :=
  ⟨encBool, Decoder.bool, encBits, Decoder.bits⟩

private def windowPartyPort : WordPort (Fin 2 × Bool) (Option (List Bool)) :=
  WordPort.party (n := 2) windowInputPort

private def msgPort : WordPort (List Bool) (List Bool) :=
  ⟨encBits, Decoder.bits, encBits, Decoder.bits⟩

private def encFin2 : Fin 2 ↪ List Bool :=
  ⟨fun i => encUnary i.val, fun _ _ h => Fin.val_injective (encUnary.injective h)⟩

private def unaryCodec : WordCodec ℕ where
  enc := encUnary
  decode := Decoder.unary.decode
  decode_enc := Decoder.unary.decode_enc

private noncomputable def emptyWordOracle :
    WordInterface.empty.Channel × List Bool → StateT Unit PMF (List Bool)
  | cw, _ => cw.1.elim

/-! ### 1. `windowStore` ideal functionality witness -/

section WindowStoreWitness

/-- Two-party functionality storing `(κ, log)`: party `0` samples a uniform coin `c`, prepends
`b ^^ c` to the log (unbounded state growth), party `1` returns the most recent `κ` bits
(`s.take κ`), and the backdoor is a no-op. -/
private noncomputable def windowStore : IdealFunctionality 2 Bool (List Bool) Unit Unit where
  State := ℕ × List Bool
  init κ _ := pure (κ, [])
  onInput i b := do
    let (κ, s) ← get
    if i = 0 then
      let c ← StateT.lift (ProbComp.uniform Bool)
      set (κ, (b ^^ c) :: s)
      return none
    else
      return some (s.take κ)
  onBackdoor _ := return ()

private theorem windowStore_onInput_zero_eval (b : Bool) (st : ℕ × List Bool) :
    ((windowStore.onInput (0 : Fin 2) b).run st).eval =
      PMF.map (fun c : Bool => ((none : Option (List Bool)), (st.1, (b ^^ c) :: st.2)))
        (ProbComp.uniform Bool).eval := by
  change (do
      let x ← (pure (st, st) : ProbComp _)
      let y ← ((fun c => (c, x.2)) <$> ProbComp.uniform Bool)
      let z ← (pure ((), (x.1.1, (b ^^ y.1) :: x.1.2)) : ProbComp _)
      pure ((none : Option (List Bool)), z.2)).eval =
    PMF.map (fun c : Bool => ((none : Option (List Bool)), (st.1, (b ^^ c) :: st.2)))
      (ProbComp.uniform Bool).eval
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, PMF.pure_bind,
    PMF.bind_map]
  rfl

private theorem windowStore_onInput_one_eval (b : Bool) (st : ℕ × List Bool) :
    ((windowStore.onInput (1 : Fin 2) b).run st).eval =
      PMF.pure ((some (st.2.take st.1) : Option (List Bool)), st) := by
  have hne : (1 : Fin 2) ≠ 0 := by decide
  change (do
      let x ← (pure (st, st) : ProbComp _)
      if (1 : Fin 2) = 0 then
        let y ← ((fun c => (c, x.2)) <$> ProbComp.uniform Bool)
        let z ← (pure ((), (x.1.1, (b ^^ y.1) :: x.1.2)) : ProbComp _)
        pure ((none : Option (List Bool)), z.2)
      else
        pure ((some (x.1.2.take x.1.1) : Option (List Bool)), x.2)).eval =
    PMF.pure ((some (st.2.take st.1) : Option (List Bool)), st)
  simp only [hne, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]

private theorem windowStore_onBackdoor_eval (u : Unit) (st : ℕ × List Bool) :
    ((windowStore.onBackdoor u).run st).eval = PMF.pure ((), st) := by
  change (pure ((), st) : ProbComp _).eval = PMF.pure ((), st)
  exact ProbComp.eval_pure ((), st)

private theorem windowStore_onInput_zero_support (b : Bool) (st : windowStore.State)
    (r : Option (List Bool) × windowStore.State) :
    r ∈ ((windowStore.onInput (0 : Fin 2) b).run st).eval.support ↔
      ∃ c : Bool, r.1 = none ∧
        r.2 = ((st : ℕ × List Bool).1, (b ^^ c) :: (st : ℕ × List Bool).2) := by
  let st' : ℕ × List Bool := st
  let r' : Option (List Bool) × ℕ × List Bool := (r.1, r.2)
  have h : ((windowStore.onInput (0 : Fin 2) b).run st).eval r =
      (PMF.map (fun c : Bool => ((none : Option (List Bool)), (st'.1, (b ^^ c) :: st'.2)))
        (ProbComp.uniform Bool).eval) r' :=
    congrFun (congrArg DFunLike.coe (windowStore_onInput_zero_eval b st')) r'
  rw [PMF.mem_support_iff, h, ← PMF.mem_support_iff, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨c, (congrArg Prod.fst hc).symm, (congrArg Prod.snd hc).symm⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, by simp [ProbComp.eval_uniform], Prod.ext h1.symm h2.symm⟩

private def windowStoreCodec : WordCodec (ℕ × List Bool) where
  enc := encPair encUnary encBits
  decode := (Decoder.pair Decoder.unary Decoder.bits).decode
  decode_enc := (Decoder.pair Decoder.unary Decoder.bits).decode_enc

private theorem windowStore_onInput_isPPTOn :
    IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
      (IdealFunctionality.wordStep windowPartyPort windowStoreCodec
        fun q => windowStore.onInput q.1 q.2) := by
  have hdecReq : ComputableInPolyTime
      (fun p : List Bool × List Bool => windowPartyPort.queryDecoder.decode p.1)
      (encPair encBits encBits) (encPair encFin2 encBool) :=
    windowPartyPort.queryDecoder.computableInPolyTime.comp
      (ComputableInPolyTime.fst encBits encBits)
  have hdecState := (Decoder.pair Decoder.unary Decoder.bits).computableInPolyTime.comp
    (ComputableInPolyTime.snd encBits encBits)
  have hcond : ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        decide ((windowPartyPort.queryDecoder.decode p.1).1 = 0))
      (encPair encBits encBits) encBool :=
    (ComputableInPolyTime.of_finite (fun i : Fin 2 => decide (i = 0))).comp
      ((ComputableInPolyTime.fst encFin2 encBool).comp hdecReq)
  have hyes : IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
      (fun p =>
        (fun c => (windowPartyPort.reply none,
          windowStoreCodec.enc ((windowStoreCodec.decode p.2).1,
            ((windowPartyPort.queryDecoder.decode p.1).2 ^^ c) ::
              (windowStoreCodec.decode p.2).2))) <$> ProbComp.uniform Bool) := by
    refine (isPPTOn_uniform_bool (encPair encBits encBits)).map_with ?_
    have hbit := ((ComputableInPolyTime.snd encFin2 encBool).comp hdecReq).comp
      (ComputableInPolyTime.fst (encPair encBits encBits) encBool)
    have hxor := ComputableInPolyTime.bool_xor.comp
      (hbit.prod (ComputableInPolyTime.snd (encPair encBits encBits) encBool))
    have hhead := (ComputableInPolyTime.of_finite (fun b : Bool => [b]) (encIn := encBool)
      (encOut := encBits)).comp hxor
    have hst := hdecState.comp (ComputableInPolyTime.fst (encPair encBits encBits) encBool)
    have hlist := ComputableInPolyTime.bitsAppend hhead
      ((ComputableInPolyTime.snd encUnary encBits).comp hst)
    have hencSt := (ComputableInPolyTime.of_eq (encIn := encPair encUnary encBits)
      (encOut := encBits) (fun _ => rfl)).comp
      (((ComputableInPolyTime.fst encUnary encBits).comp hst).prod hlist)
    exact (ComputableInPolyTime.const (windowPartyPort.reply none)).prod hencSt
  have hno : IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
      (fun p => pure (windowPartyPort.reply (some
        ((windowStoreCodec.decode p.2).2.take (windowStoreCodec.decode p.2).1)),
        windowStoreCodec.enc (windowStoreCodec.decode p.2))) := by
    have htake := ComputableInPolyTime.bitsTakeWithInput
      ((ComputableInPolyTime.snd encUnary encBits).comp hdecState)
      ((ComputableInPolyTime.fst encUnary encBits).comp hdecState)
    have hsome : ComputableInPolyTime
        (fun p : List Bool × List Bool =>
          some ((windowStoreCodec.decode p.2).2.take (windowStoreCodec.decode p.2).1))
        (encPair encBits encBits) (encOption encBits) := by
      fun_prop
    have hrep := (ComputableInPolyTime.of_eq (encIn := encOption encBits) (encOut := encBits)
      (fun _ => rfl)).comp hsome
    have hnorm := (ComputableInPolyTime.of_eq (encIn := encPair encUnary encBits)
      (encOut := encBits) (fun _ => rfl)).comp hdecState
    exact (hrep.prod hnorm).isPPTOn
  refine (IsPPTOn.ite
    (condition := fun p => (windowPartyPort.queryDecoder.decode p.1).1 = 0)
    hcond hyes hno).congr fun p => ?_
  dsimp only [IdealFunctionality.wordStep]
  by_cases hi : (windowPartyPort.queryDecoder.decode p.1).1 = 0
  · simp only [hi, ↓reduceIte, ProbComp.eval_map]
    change _ = PMF.map (fun result : Option (List Bool) × ℕ × List Bool =>
      (windowPartyPort.reply result.1, windowStoreCodec.enc result.2))
      ((windowStore.onInput 0 (windowPartyPort.queryDecoder.decode p.1).2).run
        (windowStoreCodec.decode p.2)).eval
    rw [windowStore_onInput_zero_eval, PMF.map_comp]
    rfl
  · have hi1 : (windowPartyPort.queryDecoder.decode p.1).1 = 1 := by omega
    simp only [hi, ↓reduceIte, ProbComp.eval_pure, ProbComp.eval_map]
    rw [hi1]
    change _ = PMF.map (fun result : Option (List Bool) × ℕ × List Bool =>
      (windowPartyPort.reply result.1, windowStoreCodec.enc result.2))
      ((windowStore.onInput 1 (windowPartyPort.queryDecoder.decode p.1).2).run
        (windowStoreCodec.decode p.2)).eval
    rw [windowStore_onInput_one_eval, PMF.pure_map]

private noncomputable def windowStoreCert :
    IdealFunctionality.PPTCertificate windowStore windowPartyPort unitPort where
  stateCodec := windowStoreCodec
  init := by
    have hpair := (ComputableInPolyTime.fst encUnary (encFinite (Finset (Fin 2)))).prod
      (ComputableInPolyTime.const (encIn := encPair encUnary (encFinite (Finset (Fin 2))))
        (encOut := encBits) [])
    have hcomp := (ComputableInPolyTime.of_eq (encIn := encPair encUnary encBits)
      (encOut := encBits) (fun _ => rfl)).comp hpair
    exact hcomp.isPPTOn.congr fun p => by
      simp only [windowStore, ProbComp.eval_pure]
      rfl
  onInput := windowStore_onInput_isPPTOn
  onBackdoor := by
    have hnorm := (ComputableInPolyTime.of_eq (encIn := encPair encUnary encBits)
      (encOut := encBits) (fun _ => rfl)).comp
      ((Decoder.pair Decoder.unary Decoder.bits).computableInPolyTime.comp
        (ComputableInPolyTime.snd encBits encBits))
    exact ((ComputableInPolyTime.const (unitPort.reply ())).prod hnorm).isPPTOn.congr fun p => by
      simp only [IdealFunctionality.wordStep, ProbComp.eval_pure, ProbComp.eval_map]
      change _ = PMF.map (fun result : Unit × ℕ × List Bool =>
        (unitPort.reply result.1, windowStoreCodec.enc result.2))
        ((windowStore.onBackdoor (unitPort.queryDecoder.decode p.1)).run
          (windowStoreCodec.decode p.2)).eval
      rw [windowStore_onBackdoor_eval, PMF.pure_map]
      rfl
  normalize :=
    (ComputableInPolyTime.of_eq (encIn := encPair encUnary encBits) (encOut := encBits)
      (fun _ => rfl)).comp (Decoder.pair Decoder.unary Decoder.bits).computableInPolyTime
  growth _ := 1
  growth_poly := PolyBounded.const 1
  preserve_onInput req st result hr := by
    let st' : ℕ × List Bool := st
    by_cases hi : (windowPartyPort.queryDecoder.decode req).1 = 0
    · rw [hi, windowStore_onInput_zero_support] at hr
      rcases hr with ⟨c, _, hs⟩
      let r2 : ℕ × List Bool := result.2
      have hs' : r2 = (st'.1, ((windowPartyPort.queryDecoder.decode req).2 ^^ c) :: st'.2) := hs
      change (encPair encUnary encBits r2).length ≤ (encPair encUnary encBits st').length + 1
      rw [hs']
      simp only [length_encPair, encBits_apply, List.length_cons]
      omega
    · have hi1 : (windowPartyPort.queryDecoder.decode req).1 = 1 := by omega
      let r' : Option (List Bool) × ℕ × List Bool := (result.1, result.2)
      have h : ((windowStore.onInput (windowPartyPort.queryDecoder.decode req).1
          (windowPartyPort.queryDecoder.decode req).2).run st).eval result =
          (PMF.pure ((some (st'.2.take st'.1) : Option (List Bool)), st')) r' := by
        rw [hi1]
        exact congrFun (congrArg DFunLike.coe (windowStore_onInput_one_eval _ st')) r'
      rw [PMF.mem_support_iff, h, ← PMF.mem_support_iff, PMF.mem_support_pure_iff] at hr
      change (windowStoreCodec.enc r'.2).length ≤ (windowStoreCodec.enc st').length + 1
      rw [congrArg Prod.snd hr]
      exact Nat.le_add_right _ _
  preserve_onBackdoor req st result hr := by
    let st' : ℕ × List Bool := st
    let r' : Unit × ℕ × List Bool := (result.1, result.2)
    have h : ((windowStore.onBackdoor (unitPort.queryDecoder.decode req)).run st).eval result =
        (PMF.pure ((), st')) r' :=
      congrFun (congrArg DFunLike.coe (windowStore_onBackdoor_eval _ st')) r'
    rw [PMF.mem_support_iff, h, ← PMF.mem_support_iff, PMF.mem_support_pure_iff] at hr
    change (windowStoreCodec.enc r'.2).length ≤ (windowStoreCodec.enc st').length + 1
    rw [congrArg Prod.snd hr]
    exact Nat.le_add_right _ _

/-- `windowStore` is a strict-PPT ideal functionality. -/
theorem windowStore_isPPT : windowStore.IsPPT windowPartyPort unitPort :=
  ⟨windowStoreCert⟩

/-- Lifting `windowStore` via `IdealFunctionality.IsPPT.toProtocol` gives a strict-PPT protocol. -/
theorem windowStore_toProtocol_isPPT : windowStore.toProtocol.IsPPT windowPartyPort unitPort :=
  windowStore_isPPT.toProtocol

end WindowStoreWitness

/-! ### 2. `corruptRouter` branches and certificate witness -/

section CorruptRouterWitness

/-- Under `corruptRouter {1} (windowStore.toProtocol κ {1})`, environment inputs to corrupted party
`1` return `none` without changing state, adversary-routed inputs to party `1` forward to
`windowStore`, and environment inputs to honest party `0` reach `windowStore`. -/
theorem windowStore_corruptRouter_branches (κ : ℕ) (b : Bool) :
    (corruptRouter ({1} : Finset (Fin 2)) (windowStore.toProtocol κ {1})).handle
        (Sum.inl ((1 : Fin 2), b)) = pure none ∧
    (corruptRouter ({1} : Finset (Fin 2)) (windowStore.toProtocol κ {1})).handle
        (Sum.inr (.inl ((1 : Fin 2), b))) =
      Sum.inl <$> (windowStore.toProtocol κ {1}).handle (Sum.inl ((1 : Fin 2), b)) ∧
    (corruptRouter ({1} : Finset (Fin 2)) (windowStore.toProtocol κ {1})).handle
        (Sum.inl ((0 : Fin 2), b)) =
      (windowStore.toProtocol κ {1}).handle (Sum.inl ((0 : Fin 2), b)) := by
  have h1 : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by decide
  have h0 : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp [corruptRouter, h1]; rfl
  · simp [corruptRouter, h1]
  · simp [corruptRouter, h0]

/-- Concrete routed poll evaluation on `corruptRouter {1} (windowStore.toProtocol κ {1})`: an
adversary-routed poll at corrupted party `1` returns `Sum.inl (some (st.2.take st.1))` without
modifying state. -/
theorem windowStore_corruptRouter_adv_poll_eval (κ : ℕ) (b : Bool) (st : ℕ × List Bool) :
    ProbOracleComp.runWith emptyWordOracle
        (ProbOracleComp.lowerWith WordInterface.empty 0
          (((corruptRouter ({1} : Finset (Fin 2)) (windowStore.toProtocol κ {1})).handle
            (Sum.inr (.inl ((1 : Fin 2), b)))).run st)) () =
      PMF.pure (((Sum.inl (some (st.2.take st.1)) : RoutedNetR (List Bool) Unit), st), ()) := by
  rw [(windowStore_corruptRouter_branches κ b).2.1]
  let st' : windowStore.State := st
  have hev : ((windowStore.onInput (1 : Fin 2) b).run st').eval =
      PMF.pure ((some (st.2.take st.1) : Option (List Bool)), st') :=
    windowStore_onInput_one_eval b st
  change ProbOracleComp.runWith emptyWordOracle
      (ProbOracleComp.lowerWith WordInterface.empty 0
        (Prod.map Sum.inl id <$>
          ProbOracleComp.sample ((windowStore.onInput (1 : Fin 2) b).run st'))) () = _
  rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_map, ProbOracleComp.simulate_sample,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_sample, hev, PMF.pure_map, PMF.pure_map]
  rfl

/-- Static-corruption routing around `windowStore.toProtocol` preserves `Protocol.IsPPT`, using
`WordPort.computable_partyIndex` to extract the party index from `windowPartyPort`. -/
theorem windowStore_corruptRouter_isPPT :
    Protocol.IsPPT (fun κ C => corruptRouter C (windowStore.toProtocol κ C))
      windowPartyPort (WordPort.sum windowPartyPort unitPort) :=
  windowStore_toProtocol_isPPT.corruptRouter (WordPort.computable_partyIndex windowInputPort)

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
    let EIn := encHandlerCall (encPPTParam 2) (encFinite (WordInterface.net msgPort).Channel)
      encBits
    let iN := WordInterface.net msgPort
    have hq : IsOraclePPTOn EIn encBits
        (fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool =>
          iN.reply (iN.decodeQuery x.2.1.1 x.2.1.2) <$>
            ProbOracleComp.lowerWith iN x.1.replyBound
              (ProbOracleComp.query (iN.decodeQuery x.2.1.1 x.2.1.2))) := by
      refine iN.isOraclePPTOn_lowerWith_query
        (query := fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool =>
          iN.decodeQuery x.2.1.1 x.2.1.2)
        (limit := fun x => x.1.replyBound) ?_ ?_ ?_
      · have heq : (fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool =>
            iN.channel (iN.decodeQuery x.2.1.1 x.2.1.2)) = fun x => x.2.1.1 :=
          funext fun x => (iN.request_decodeQuery x.2.1.1 x.2.1.2).1
        rw [heq]; unfold EIn encHandlerCall; fun_prop
      · have heq : (fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool =>
            iN.request (iN.decodeQuery x.2.1.1 x.2.1.2)) =
            fun x => iN.requestNormalize x.2.1.1 x.2.1.2 :=
          funext fun x => (iN.request_decodeQuery x.2.1.1 x.2.1.2).2
        rw [heq]
        have hproj : ComputableInPolyTime
            (fun x : PPTParam 2 × (iN.Channel × List Bool) × List Bool => x.2.1)
            EIn (encPair (encFinite iN.Channel) encBits) := by
          unfold EIn encHandlerCall; fun_prop
        exact iN.computable_requestNormalize.comp hproj
      · unfold EIn encHandlerCall; fun_prop
    have hsucc : ComputableInPolyTime
        (fun pair : (PPTParam 2 × (iN.Channel × List Bool) × List Bool) × List Bool =>
          (pair.2, encUnary (Decoder.unary.decode pair.1.2.2 + 1)))
        (encPair EIn encBits) (encPair encBits encBits) := by
      have hsw : ComputableInPolyTime
          (fun pair : (PPTParam 2 × (iN.Channel × List Bool) × List Bool) × List Bool =>
            Decoder.unary.decode pair.1.2.2)
          (encPair EIn encBits) encUnary := by
        refine Decoder.unary.computableInPolyTime.comp ?_
        unfold EIn encHandlerCall; fun_prop
      have hinc := (ComputableInPolyTime.of_eq (encIn := encUnary) (encOut := encBits)
        (fun _ => rfl)).comp
        (ComputableInPolyTime.unary_add.comp (hsw.prod (ComputableInPolyTime.const 1)))
      exact (ComputableInPolyTime.snd EIn encBits).prod hinc
    refine (hq.keep_input.map hsucc).congr fun x State oracle s => ?_
    rcases x with ⟨p, ⟨⟨⟩, w⟩, sw⟩
    rw [logAdv_wordHandle_eq]
    rfl
  normalize :=
    (ComputableInPolyTime.of_eq (encIn := encUnary) (encOut := encBits) (fun _ => rfl)).comp
      (Decoder.unary.computableInPolyTime.comp (ComputableInPolyTime.snd _ _))
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
`WordInterface.exec windowPartyPort msgPort`. -/
theorem logAdv_liftAdversary_isPPT :
    Machine.IsPPTFamily (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
      (WordInterface.protocol windowPartyPort msgPort)
      (WordInterface.exec windowPartyPort msgPort) :=
  logAdv_isPPT.liftAdversary

/-- On `liftAdversary (logAdv κ C)`, a party-channel word activation forwards on the left channel
and re-encodes even an off-image state word `[false]` into `Set.range encUnary` (`≠ [false]`). -/
theorem logAdv_liftAdversary_forwards_party_and_normalizes (p : PPTParam 2) (w : List Bool) :
    let cert := logAdvCert.liftAdversary windowPartyPort
    let iIn := WordInterface.protocol windowPartyPort msgPort
    let iOut := WordInterface.exec windowPartyPort msgPort
    let noneOracle : iIn.Channel × List Bool → StateT Unit PMF (List Bool) :=
      fun _ _ => PMF.pure (windowPartyPort.reply none, ())
    (∀ sw : List Bool,
      wordHandle (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
          iIn iOut cert.codec p (.inl (), w) sw =
        (fun r => (windowPartyPort.reply r, encUnary (Decoder.unary.decode sw))) <$>
          ProbOracleComp.lowerWith iIn p.replyBound
            (ProbOracleComp.query
              (spec := protocolSpec 2 Bool (List Bool) (List Bool) (List Bool))
              (.inl (windowPartyPort.queryDecoder.decode w)))) ∧
    (encUnary (Decoder.unary.decode [false]) ≠ [false] ∧
      ProbOracleComp.runWith noneOracle
        (wordHandle (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
          iIn iOut cert.codec ⟨p.secParam, 1, p.corrupted⟩ (.inl (), w) [false]) () =
      PMF.pure ((windowPartyPort.reply none, encUnary (Decoder.unary.decode [false])), ())) := by
  have hfwd : ∀ (q : PPTParam 2) (sw : List Bool),
      wordHandle (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
          (WordInterface.protocol windowPartyPort msgPort)
          (WordInterface.exec windowPartyPort msgPort)
          (logAdvCert.liftAdversary windowPartyPort).codec q (.inl (), w) sw =
        (fun r => (windowPartyPort.reply r, encUnary (Decoder.unary.decode sw))) <$>
          ProbOracleComp.lowerWith (WordInterface.protocol windowPartyPort msgPort) q.replyBound
            (ProbOracleComp.query
              (spec := protocolSpec 2 Bool (List Bool) (List Bool) (List Bool))
              (.inl (windowPartyPort.queryDecoder.decode w))) := by
    intro q sw
    simp only [wordHandle, liftAdversary, Machine.liftRight, PPTCertificate.liftAdversary,
      PPTCertificate.liftRight, logAdvCert, StateT.run, ProbOracleComp.lowerWith]
    rfl
  refine ⟨hfwd p, ?_, ?_⟩
  · intro h
    have hmem : false ∈ ([false] : List Bool) := by simp
    rw [← h, encUnary_apply] at hmem
    simp at hmem
  · have htake : List.take 1 (windowPartyPort.reply (none : Option (List Bool))) =
        windowPartyPort.reply none := by
      rw [List.take_of_length_le]
      simp [windowPartyPort, WordPort.party, encOption_none]
    have hfwd2 := hfwd ⟨p.secParam, 1, p.corrupted⟩ [false]
    dsimp only at hfwd2
    change ProbOracleComp.runWith _
        (wordHandle (fun κ C => liftAdversary (In := Bool) (Out := List Bool) (logAdv κ C))
          (WordInterface.protocol windowPartyPort msgPort)
          (WordInterface.exec windowPartyPort msgPort)
          (logAdvCert.liftAdversary windowPartyPort).codec ⟨p.secParam, 1, p.corrupted⟩
          (.inl (), w) [false]) () = _
    rw [hfwd2, ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, WordInterface.lowerQuery]
    rw [ProbOracleComp.runWith_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query]
    rw [PMF.pure_map, PMF.pure_map, PMF.pure_map]
    simp only [WordInterface.protocol, WordInterface.sum, WordInterface.net,
      htake, windowPartyPort.replyDecoder.decode_enc]
    rfl

end LiftAdversaryWitness

end CslibFrontierTests.Crypto.UCPPTWrappers
