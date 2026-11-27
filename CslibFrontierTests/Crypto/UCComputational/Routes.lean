/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: local-only (test)

public import CslibFrontierTests.Crypto.UCComputational.Reduction
public import Mathlib.Tactic.NormNum

/-!
# Testing computational replacement on both UC routes

The tester sends `Set(true)`, then tries the ordinary and adversarially routed child inputs.
For an honest party only the ordinary route releases the challenge. For a corrupted party
only the routed input releases it. With command translation the tag test agrees. Forwarding
the command verbatim produces advantage one on the very same admitted tester. A second
observation reads the challenge, giving advantage one half for an all-zero generator at
security parameter one.
-/

public section

namespace CslibFrontierTests.Crypto.UCComputational.Caller

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

open Primitive (serviceParty)

abbrev Word := List Bool
abbrev Result := Option (Word × Word)

@[expose] def probeParent (observe : Result → Bool)
    : HybridProtocol 1 Unit Bool Unit Unit Word (Word × Word) := fun _ _ => {
  State := PUnit
  init := pure PUnit.unit
  handle
    | .inl _ => fun s => (fun r => (some (observe r), s)) <$>
        ProbOracleComp.query (spec := partySpec 1 Word (Word × Word)) (0, [])
    | .inr _ => fun s => pure ((), s) }

@[expose] def party : WordPort (Fin 1 × Unit) (Option Bool) :=
  WordPort.party ⟨encUnit, Primitive.sampleUnitDecoder, encBool, Decoder.bool⟩
@[expose] def raw : WordPort Unit Unit :=
  ⟨encUnit, Primitive.sampleUnitDecoder, encUnit, Primitive.sampleUnitDecoder⟩

/-- The parent may apply any efficient Boolean observation to the received word pair. -/
theorem probeParent_ppt {observe : Result → Bool}
    (hobs : ComputableInPolyTime observe serviceParty.reply encBool) :
    (probeParent observe).IsPPT party raw serviceParty := by
  let iE := WordInterface.protocol party raw
  let iI := WordInterface.net serviceParty
  let X := PPTParam 1 × (iE.Channel × Word) × Word
  let eX := encHandlerCall (encPPTParam 1) (encFinite iE.Channel) encBits
  let call : X → WordOracleComp iI.Channel (Word × Word) := fun x =>
    (fun w => (party.reply (some (observe (serviceParty.replyDecoder.decode w))),[])) <$>
      (List.take x.1.replyBound <$> ProbOracleComp.query ((),serviceParty.query (0,[])))
  have hq := IsOraclePPTOn.query_take (Operation := iI.Channel) ()
    (ComputableInPolyTime.const (encIn := eX) (encOut := encBits) (serviceParty.query (0,[])))
    (by fun_prop : ComputableInPolyTime (fun x : X => x.1.replyBound) eX encUnary)
  have assemble := (((ComputableInPolyTime.optionSome encBool).comp
    (hobs.comp serviceParty.replyDecoder.computableInPolyTime)).encoding_comp).prod
    (ComputableInPolyTime.const (encIn := encBits) (encOut := encBits) ([] : Word))
  have hc : IsOraclePPTOn eX (encPair encBits encBits) call := hq.map assemble
  let branches : iE.Channel → X → WordOracleComp iI.Channel (Word × Word) := fun c =>
    match c with
    | .inl _ => call
    | .inr _ => fun _ => pure (raw.reply (), [])
  have htag : ComputableInPolyTime (fun x : X => x.2.1.1) eX (encFinite iE.Channel) := by
    unfold eX encHandlerCall; fun_prop
  have h := IsOraclePPTOn.finite_cases (branch := branches) htag (by
    rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    · exact hc
    · exact (ComputableInPolyTime.const (encIn := eX) (encOut := encPair encBits encBits)
        (raw.reply (), ([] : Word))).isPPTOn.isOraclePPTOn)
  refine ⟨{ codec := fun _ _ => punitWordCodec
            init := (ComputableInPolyTime.const (encIn := encPPTParam 1)
               (encOut := encBits) []).isPPTOn
            normalize := ComputableInPolyTime.const (encIn := encPair (encPPTParam 1) encBits) []
            growth _ _ := 0
            growth_poly := PolyBounded.const 0
            handle := ?_
            preserve := ?_ }⟩
  · apply h.congr
    rintro ⟨p,⟨c,w⟩,s⟩ σ o t
    rcases c with ⟨⟩ | ⟨⟩
    · apply congrArg (fun prog => ProbOracleComp.runWith o prog t)
      simp [wordHandle, branches, call, probeParent, iI, iE, WordInterface.protocol,
        WordInterface.sum,
        WordInterface.net, ProbOracleComp.lowerWith, ProbOracleComp.simulate_query,
        WordInterface.lowerQuery, punitWordCodec, StateT.run, map_eq_bind_pure_comp, bind_assoc]
      rfl
    · rfl
  · intro p q s out hout
    obtain ⟨y, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hout
    rfl

end CslibFrontierTests.Crypto.UCComputational.Caller

namespace CslibFrontierTests.Crypto.UCComputational.Test

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

open Primitive (SamplePort sampleWire)
open Child (Word Result)

theorem combine {channel : Type} [DecidableEq channel]
    {f g : EnvParam → WordOracleComp channel Bool}
    (op : Bool → Bool → Bool)
    (hf : IsOraclePPTOn encEnvParam encBool f) (hg : IsOraclePPTOn encEnvParam encBool g) :
    IsOraclePPTOn encEnvParam encBool (fun e => do
      let x ← f e
      let y ← g e
      return op x y) := by
  let D := encPair encEnvParam encBool
  have keep := (ComputableInPolyTime.snd encEnvParam encBool).comp
    (ComputableInPolyTime.fst D encBool)
  have finish := (ComputableInPolyTime.of_finite (encOut := encBool)
      (fun p : Bool × Bool => op p.1 p.2)).comp
    (keep.prod (ComputableInPolyTime.snd D encBool))
  have h := (hg.preprocess (ComputableInPolyTime.fst encEnvParam encBool)).map_with
    (f := fun (t : EnvParam × Bool) y => op t.2 y) finish
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    hf.bind_with (output := encBool) (second := fun e x => (fun y => op x y) <$> g e) h

theorem release_length {α σ S : Type} {overhead : ℕ} (next : S) (reply : Word → α) (width : α → ℕ)
    (hw : ∀ w, width (reply w) ≤ w.length + overhead) (b : ℕ)
    (oracle : sampleWire.Channel × Word → StateT σ PMF Word) (sO : σ)
    (x : (α × S) × σ)
    (hx : x ∈ (ProbOracleComp.runWith oracle (ProbOracleComp.lowerWith sampleWire b (do
      let w ← ProbOracleComp.query (spec := SamplePort) ()
      pure (reply w, next))) sO).support) : width x.1.1 ≤ b + overhead := by
  have hs := ProbOracleComp.mem_support_of_mem oracle hx
  simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pure,
    ProbOracleComp.simulate_query, WordInterface.lowerQuery] at hs
  obtain ⟨w, poss, ret⟩ := OracleComp.mem_supportWith_bind_iff.mp hs
  obtain ⟨v, pv, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp poss
  obtain ⟨u, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp pv
  have hx' := OracleComp.eq_of_mem_supportWith_pure ret
  rw [hx']
  exact (hw _).trans (Nat.add_le_add_right (List.length_take_le b u) overhead)

abbrev party := Caller.party
abbrev raw := Caller.raw
abbrev net := Computational.outerNetPort party raw Child.party Child.raw
abbrev OQ := RoutedNetQ 1 Unit (Unit ⊕ Child.Q)
abbrev ORsp := RoutedNetR Bool (Unit ⊕ Child.R)
abbrev Ports := execSpec 1 Unit Bool OQ ORsp
abbrev A := dummyAdversary 1 OQ ORsp
abbrev S := compSim (hybridSim (In := Unit) (Out := Bool) (NetQ := Unit) (NetR := Unit)
  Child.relay) A

@[expose] def observe (checkWord : Bool) (r : Option Result) : Bool :=
  let v := r.getD ([], [])
  v.1.headD false && (!checkWord || !(v.2.headD false))

abbrev parent (checkWord : Bool) := Caller.probeParent (observe checkWord)

private theorem observe_ppt (checkWord : Bool) :
    ComputableInPolyTime (observe checkWord) Child.party.reply encBool := by
  let pair := encPair encBits encBits
  have val : ComputableInPolyTime (fun r : Option Result => r.getD ([],[])) (encOption pair) pair :=
    ComputableInPolyTime.id'.optionGetDWithInput (.const ([],[]))
  have head := ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false
  have tag := head.comp ((ComputableInPolyTime.fst encBits encBits).comp val)
  have coin := head.comp ((ComputableInPolyTime.snd encBits encBits).comp val)
  exact ComputableInPolyTime.bool_and' tag (ComputableInPolyTime.bool_or'
    (ComputableInPolyTime.const (!checkWord)) (ComputableInPolyTime.bool_not.comp coin))

theorem parent_ppt (checkWord : Bool) : (parent checkWord).IsPPT party raw Child.party :=
  Caller.probeParent_ppt (observe_ppt checkWord)

abbrev setCmd : OQ := .inr (.inr (.inr true))
abbrev readRoute : OQ := .inr (.inr (.inl (0,[])))

@[expose] def readNet (b : Bool) : ORsp → Bool
  | .inr (.inr (.inl r)) => observe b r
  | _ => false

theorem readNet_ppt (b : Bool) : ComputableInPolyTime (readNet b) net.reply encBool := by
  let child := ComputableInPolyTime.sumElim (observe_ppt b)
    (ComputableInPolyTime.const (encIn := Child.raw.reply) (encOut := encBool) false)
  let mid := ComputableInPolyTime.sumElim
    (ComputableInPolyTime.const (encIn := raw.reply) (encOut := encBool) false) child
  exact (ComputableInPolyTime.sumElim
    (ComputableInPolyTime.const (encIn := party.reply) (encOut := encBool) false)
    mid).of_enc_eq (fun r => by rcases r with _ | (_ | (_ | _)) <;> rfl)

@[expose] def test (b : Bool) : Environment 1 Unit Bool OQ ORsp := fun _ _ => do
  let _ ← ProbOracleComp.query (spec := Ports) (.inr setCmd)
  let p ← ProbOracleComp.query (spec := Ports) (.inl (0,()))
  let r ← ProbOracleComp.query (spec := Ports) (.inr readRoute)
  return (decide (p = some true) || readNet b r)

private abbrev wire := WordInterface.exec party net

theorem test_ppt (b : Bool) : (test b).IsPPT party net := by
  have hb : ComputableInPolyTime EnvParam.replyBound encEnvParam encUnary := by fun_prop
  let get (q : (Fin 1 × Unit) ⊕ OQ) (e : EnvParam) :=
    ProbOracleComp.lowerWith wire e.replyBound (ProbOracleComp.query (spec := Ports) q)
  have hppt (q : (Fin 1 × Unit) ⊕ OQ) :
      IsOraclePPTOn (Operation := wire.Channel) encEnvParam (wire.reply q) (get q) := by
    exact wire.isOraclePPTOn_lowerWith_query (query := fun _ : EnvParam => q)
      (limit := EnvParam.replyBound) (.const _) (.const _) hb
  have set := (hppt (.inr setCmd)).map
    (ComputableInPolyTime.const (encOut := encBool) false)
  have read := (hppt (.inl (0,()))).map
    (show ComputableInPolyTime (fun p => decide (p = some true)) party.reply encBool from
      ComputableInPolyTime.id'.decide_eq' (.const (some true)))
  have routed := (hppt (.inr readRoute)).map (readNet_ppt b)
  apply (Test.combine (fun _ x => x) set (Test.combine Bool.or read routed)).congr
  intro e σ o s
  apply congrArg (fun p => ProbOracleComp.runWith o p s)
  simp [get, test, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_pure, ProbOracleComp.simulate_query, map_eq_bind_pure_comp, bind_assoc]

theorem cases_set (C : Finset (Fin 1)) : C = ∅ ∨ C = {0} := by
  by_cases h : 0 ∈ C
  · right; ext i; rw [Subsingleton.elim i 0]; simp [h]
  · left; ext i; rw [Subsingleton.elim i 0]; simp [h]

abbrev T (b : Bool) (C : Finset (Fin 1)) := Computational.innerTester (parent b) C A (test b)
abbrev subPorts := execSpec 1 Word Result Child.Q Child.R
abbrev ctlQuery : (Fin 1 × Word) ⊕ Child.Q := .inr (.inr true)
abbrev ordinary : (Fin 1 × Word) ⊕ Child.Q := .inl (0,[])
abbrev routed : (Fin 1 × Word) ⊕ Child.Q := .inr (.inl (0,[]))

theorem inner_honest (b : Bool) (κ : ℕ) (z : Word) :
    T b ∅ κ z = (do
      let _ ← ProbOracleComp.query (spec := subPorts) ctlQuery
      let a ← ProbOracleComp.query (spec := subPorts) ordinary
      let t ← ProbOracleComp.query (spec := subPorts) routed
      return decide (some (observe b a) = some true) || readNet b (.inr (.inr t))) := rfl

theorem inner_corrupt (b : Bool) (κ : ℕ) (z : Word) :
    T b {0} κ z = (do
      let _ ← ProbOracleComp.query (spec := subPorts) ctlQuery
      let t ← ProbOracleComp.query (spec := subPorts) routed
      return decide ((none : Option Bool) = some true) || readNet b (.inr (.inr t))) := rfl

abbrev wrapped (inv : Bool) (C : Finset (Fin 1)) (κ : ℕ) :=
  routeCorrupt C ((Child.service inv).toMachine κ C)

@[expose] def decision (inv b : Bool) : Word → Bool := fun w => !inv && (!b || !(w.headD false))

/-- Removing the private resource leaves exactly one read on either route. With
an untranslated command the wire bit is false throughout the inverted game. -/
theorem open_trace (inv b : Bool) (C : Finset (Fin 1)) (κ : ℕ) (z : Word) :
    (wrapped inv C κ).link (T b C κ z) = (decision inv b) <$>
      ProbOracleComp.query (spec := Primitive.SamplePort) () := by
  rcases cases_set C with rfl | rfl
  · rw [inner_honest]
    change (fun w : Word => decide (some (observe b (some ([if inv then false else true],w))) =
      some true) || readNet b (.inr (.inr (.inl none)))) <$>
      ProbOracleComp.query (spec := Primitive.SamplePort) () = _
    unfold decision
    cases inv <;> cases b <;> simp [observe, readNet]
  · rw [inner_corrupt]
    change (fun w : Word => decide ((none : Option Bool) = some true) ||
      readNet b (.inr (.inr (.inl (some ([if inv then false else true],w)))))) <$>
      ProbOracleComp.query (spec := Primitive.SamplePort) () = _
    unfold decision
    cases inv <;> cases b <;> simp [observe, readNet]

theorem full_trace (inv b : Bool) (draw : Computational.Sampler) (C : Finset (Fin 1))
    (κ : ℕ) (z : Word) :
    exec (compose (parent b) (Child.protocol inv draw)) A C (test b) κ z =
      decision inv b <$> draw κ := by
  rw [exec_eq_exec_dummy (compose (parent b) _) A, exec_compose_dummy,
    Child.protocol, HybridFunctionality.exec_close, Primitive.resource_run]
  simp only [absorbAdversary, dummyAdversary, Machine.liftRight_id, Machine.link_id]
  change (draw κ >>= fun r => Primitive.answer ((wrapped inv C κ).link (T b C κ z)) r) = _
  rw [open_trace]
  simp [Primitive.answer, map_eq_bind_pure_comp]

theorem translated_law (b : Bool) (draw aux : Computational.Sampler) (C : Finset (Fin 1)) (κ : ℕ) :
    Computational.sampled (exec (compose (parent b) (Child.protocol true draw))
      S C (test b)) aux κ = (decision false b <$> draw κ).eval := by
  rw [← Application.translation_full (parent b) draw aux A C (test b) κ]
  simp only [Computational.sampled, full_trace, PMF.bind_const]

theorem full_law (inv b : Bool) (draw aux : Computational.Sampler) (C : Finset (Fin 1))
    (κ : ℕ) :
    Computational.sampled (exec (compose (parent b) (Child.protocol inv draw))
      A C (test b)) aux κ = (decision inv b <$> draw κ).eval := by
  simp only [Computational.sampled, full_trace, PMF.bind_const]

/-- Dropping the translation loses with advantage one, independently of both private samplers. -/
theorem dropped_translation (left right aux : Computational.Sampler) (C : Finset (Fin 1)) (κ : ℕ) :
    Game.advantage (Computational.sampled (exec (compose (parent false)
      (Child.protocol false left)) A C (test false)) aux κ)
      (Computational.sampled (exec (compose (parent false) (Child.protocol true right))
        A C (test false)) aux κ) = 1 := by
  rw [full_law, full_law]
  unfold decision
  simp [ProbComp.eval_map, PMF.map, Function.comp_def, PMF.bind_const, Game.succProbability]

theorem translated_tag_agrees (left right aux : Computational.Sampler) (C : Finset (Fin 1))
    (κ : ℕ) :
    Game.advantage (Computational.sampled (exec (compose (parent false)
      (Child.protocol false left)) A C (test false)) aux κ)
      (Computational.sampled (exec (compose (parent false) (Child.protocol true right))
        S C (test false)) aux κ) = 0 := by
  rw [full_law, translated_law]
  unfold decision
  simp [ProbComp.eval_map, PMF.map, Function.comp_def, PMF.bind_const]

/-- The simulator construction and the outer adversary are kept literally in
place. Only the child translator is replaced by the child forwarder. -/
theorem forward_only_gap (left right aux : Computational.Sampler) (C : Finset (Fin 1)) (κ : ℕ) :
    Game.advantage (Computational.sampled (exec (compose (parent false)
      (Child.protocol false left)) A C (test false)) aux κ)
      (Computational.sampled (exec (compose (parent false) (Child.protocol true right))
        (compSim (hybridSim Experiment.dummy) A) C (test false)) aux κ) = 1 := by
  rw [Application.forwarding_full]
  exact dropped_translation left right aux C κ

def zeroGenerator : Primitive.GeneratorFamily := fun _ => ⟨fun _ _ => false⟩

/-- The second observation checks the tag and the challenge's first bit. With
the required translator, the deliberately insecure zero generator still has
its first-bit gap on either path, already at security parameter one. -/
theorem combined_gap (aux : Computational.Sampler) (C : Finset (Fin 1)) :
    Game.advantage (Computational.sampled (exec (compose (parent true)
      (Child.protocol false (Primitive.generated zeroGenerator))) A C (test true)) aux 1)
      (Computational.sampled (exec (compose (parent true)
        (Child.protocol true Primitive.uniformOutput))
        S C (test true)) aux 1) = 1 / 2 := by
  rw [full_law, translated_law]
  apply NNReal.eq
  rw [Game.coe_advantage]
  have real : Game.succProbability
      ((decision false true <$> Primitive.generated zeroGenerator 1).eval) = 1 := by
    simp only [Primitive.generated, ProbComp.eval_map, PMF.map, Function.comp_def,
      PMF.bind_bind, PMF.pure_bind]
    change Game.succProbability (((BitString.sampleList 1).eval).bind fun _ => PMF.pure true) = 1
    simp [Game.succProbability, PMF.bind_const]
  have ideal : Game.succProbability
      ((decision false true <$> Primitive.uniformOutput 1).eval) = 1 / 2 := by
    rw [ProbComp.eval_map, PMF.map]
    change Game.succProbability
      (((BitString.sampleList (1 + 1)).eval).bind fun r => PMF.pure (!(r.headD false))) = 1 / 2
    rw [BitString.sampleList, ProbComp.eval_bind]
    simp only [ProbComp.eval_uniform, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
      PMF.pure_bind, List.headD_cons, PMF.bind_const]
    rw [Game.succProbability, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    norm_num [PMF.uniformOfFintype_apply, PMF.pure_apply, one_div]
    rw [show (2 : ENNReal) = ((2 : NNReal) : ENNReal) by norm_num, ENNReal.toNNReal_coe]
    norm_num
  rw [real, ideal]
  norm_num

abbrev sw := WordInterface.exec Child.party Child.network

theorem step_bound (C : Finset (Fin 1)) (κ b : ℕ)
    (q : (Fin 1 × Word) ⊕ Child.Q)
    (hq : (∃ c : Bool, q = .inr (.inr c)) ∨ q = ordinary ∨ q = routed)
    (state : Bool × Bool) {σ : Type}
    (o : Primitive.sampleWire.Channel × Word → StateT σ PMF Word) (t : σ)
    (x : (subPorts q × (Bool × Bool)) × σ)
    (hx : x ∈ (ProbOracleComp.runWith o (ProbOracleComp.lowerWith Primitive.sampleWire b
      (((wrapped false C κ).handle q).run state)) t).support) :
    (sw.reply q x.1.1).length ≤ b + 5 := by
  obtain ⟨tag, used⟩ := state
  rcases cases_set C with rfl | rfl <;> rcases hq with ⟨c,rfl⟩ | rfl | rfl <;> cases used
  all_goals first
    | change x ∈ (PMF.pure _).support at hx
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
      first | change 2 ≤ b + 5 | change 1 ≤ b + 5 | change 0 ≤ b + 5
      omega
    | exact Test.release_length (overhead := 5) (tag,true) (fun w => some ([tag],w))
        (fun a => (sw.reply ordinary a).length) (fun w => by
          simp [sw, WordInterface.exec, WordInterface.sum, WordInterface.net,
            Primitive.serviceParty, WordPort.party]) b o t x hx
    | exact Test.release_length (overhead := 5) (tag,true)
        (fun w => Sum.inl (some ([tag],w)) : Word → Child.R) (fun a => (sw.reply routed a).length)
        (fun w => by simp [sw, WordInterface.exec, WordInterface.sum, WordInterface.net,
          Child.network, WordPort.sum, Primitive.serviceParty, WordPort.party])
        b o t x hx

private theorem service_cap (b : Bool) (C : Finset (Fin 1)) :
    Experiment.ServiceCut Experiment.dummy C (T b C) := by
  refine ⟨fun e => e.replyBound + 5, by fun_prop, ?_⟩
  intro e σ o t state _
  simp only [absorbAdversary, Experiment.dummy, dummyAdversary, Machine.liftRight_id,
    Machine.link_id]
  rcases cases_set C with rfl | rfl
  · rw [inner_honest]
    apply RepliesFitOn.query
    · exact step_bound ∅ e.secParam e.replyBound ctlQuery (Or.inl ⟨true, rfl⟩) state o t
    · intro x _
      apply RepliesFitOn.query
      · exact step_bound ∅ e.secParam e.replyBound ordinary (Or.inr (Or.inl rfl)) x.1.2 o x.2
      · intro y _
        apply RepliesFitOn.query
        · exact step_bound ∅ e.secParam e.replyBound routed (Or.inr (Or.inr rfl)) y.1.2 o y.2
        · exact fun _ _ => .pure _ _ _
  · rw [inner_corrupt]
    apply RepliesFitOn.query
    · exact step_bound {0} e.secParam e.replyBound ctlQuery (Or.inl ⟨true, rfl⟩) state o t
    · intro x _
      apply RepliesFitOn.query
      · exact step_bound {0} e.secParam e.replyBound routed (Or.inr (Or.inr rfl)) x.1.2 o x.2
      · exact fun _ _ => .pure _ _ _

theorem parent_bounded (b : Bool) : Machine.IsReplyBounded (parent b)
    (WordInterface.net Child.party) (WordInterface.protocol party raw) := by
  refine ⟨fun _ => 2, PolyBounded.const 2, ?_⟩
  rintro _ (q | q) _ ⟨r, _⟩ _
  · rcases r with _ | v
    · exact Nat.zero_le _
    · cases v <;> exact le_rfl
  · cases r; exact Nat.zero_le _

theorem admitted (b : Bool) (C : Finset (Fin 1)) :
    (Application.source (parent b) party raw net).Tests party net A C (test b) := by
  refine ⟨test_ppt b, ?_, ?_, service_cap b C⟩
  · change Computational.ReplyCap (fun k set => liftAdversary (A k set))
      (WordInterface.exec party net) party net C (test b)
    apply Computational.ReplyCap.of_global
    simpa only [A, dummyAdversary, liftAdversary, Machine.liftRight_id] using
      (Machine.isReplyBounded_id (n := 1) (WordInterface.exec party net))
  · change Computational.ReplyCap (fun k set => routeCorrupt set (hybridWrap (parent b k set)))
      (WordInterface.exec Child.party Child.network) party net C
      (absorbAdversary C A (test b))
    apply Computational.ReplyCap.of_global
    exact ((parent_bounded b).hybridWrap (nq := Child.network)).routeCorrupt

theorem emulates (b : Bool) (G : Primitive.GeneratorFamily)
    (secure : G.Secure IsPPTBitStringTest) :
    Computational.EmulatesOn party net (Application.source (parent b) party raw net)
      (Application.target party raw) (compose (parent b) (Application.real G))
      (compose (parent b) Application.ideal) :=
  Application.emulates (parent b) party raw net (parent_ppt b) G secure

/-- The three reply bounds admit this tester for the computational replacement. -/
theorem close_test (b : Bool) (G : Primitive.GeneratorFamily)
    (secure : G.Secure IsPPTBitStringTest)
    (C : Finset (Fin 1)) :
    Computational.Close (exec (compose (parent b) (Application.real G)) A C (test b))
      (exec (compose (parent b) Application.ideal) S C (test b)) :=
  (Application.witness (parent b) party raw net (parent_ppt b) G secure A
    ⟨Adversary.isPPT_dummyAdversary 1 net, trivial⟩).close C (test b) (admitted b C)

end CslibFrontierTests.Crypto.UCComputational.Test
