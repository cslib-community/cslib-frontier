/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: local-only (test)

public import CslibFrontierTests.Crypto.UCComputational.Routes

/-!
# A stateful outer adversary in the one-child PRG reduction

The tester requests two setting commands. The adversary sends its saved bit on each command.
It saves the first supplied bit only if the first network acknowledgment succeeds. The tester
then asks the parent and the adversary to read. It accepts when both settings are acknowledged
and the authorized route sees the expected tag and a false first challenge bit. An empty
challenge defaults to false. The same tester is admitted for either static corruption choice.
-/

public section

namespace CslibFrontierTests.Crypto.UCComputational.Stateful

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM
open Test (OQ ORsp readRoute ordinary routed party raw net)
open Child (Word)

abbrev set (b : Bool) : OQ := .inr (.inr (.inr b))

@[expose] def ack : ORsp → Bool
  | .inr (.inr (.inr a)) => a
  | _ => false
abbrev Adv := Application.Adv Unit Bool Unit Unit (Option Bool) Bool

@[expose] def adv : Adv := fun _ _ => {
  State := Bool
  init := pure false
  handle
    | some c => fun s => (fun r => (ack r, c && ack r)) <$>
        ProbOracleComp.query (spec := netSpec OQ ORsp) (set s)
    | none => fun s => (fun r => (Test.readNet true r,s)) <$>
        ProbOracleComp.query (spec := netSpec OQ ORsp) readRoute }

abbrev sim : Adv := Application.simulator adv

def twoCommands : ProbOracleComp (netSpec (Option Bool) Bool) (Bool × Bool) := do
  let a ← ProbOracleComp.query (some true)
  let b ← ProbOracleComp.query (some false)
  return (a,b)

/-- An acknowledged first write makes the next outgoing setting true. A negative or
malformed acknowledgment makes it false. The second requested bit is false, clearing memory. -/
theorem two_commands (κ : ℕ) (C : Finset (Fin 1)) :
    (adv κ C).runFrom twoCommands false = (do
      let a ← ProbOracleComp.query (spec := netSpec OQ ORsp) (set false)
      let b ← ProbOracleComp.query (spec := netSpec OQ ORsp) (set (ack a))
      return ((ack a,ack b),false)) := by
  change (do
      let a ← ProbOracleComp.query (spec := netSpec OQ ORsp) (set false)
      let b ← ProbOracleComp.query (spec := netSpec OQ ORsp) (set (true && ack a))
      return ((ack a,ack b),false && ack b)) = _
  congr 1

theorem translated_commands (κ : ℕ) (C : Finset (Fin 1)) :
    (sim κ C).runFrom twoCommands (false,PUnit.unit) = (do
      let a ← ProbOracleComp.query (spec := netSpec OQ ORsp) (set true)
      let b ← ProbOracleComp.query (spec := netSpec OQ ORsp) (set (!(ack a)))
      return ((ack a,ack b),(false,PUnit.unit))) := by
  have tag (r : ORsp) : ack (.inr (.inr (subReply r))) = ack r := by
    rcases r with _ | (_ | _) <;> rfl
  change (do
      let a ← ProbOracleComp.query (spec := netSpec OQ ORsp) (set true)
      let ok := ack (.inr (.inr (subReply a)))
      let b ← ProbOracleComp.query (spec := netSpec OQ ORsp) (set (!(true && ok)))
      let next := ack (.inr (.inr (subReply b)))
      return ((ok,next),(false && next,PUnit.unit))) = _
  simp only [tag, Bool.false_and]
  congr 1
  funext a
  rcases a with _ | (_ | (_ | _)) <;> rfl

abbrev Ports := execSpec 1 Unit Bool (Option Bool) Bool
@[expose] def test : Environment 1 Unit Bool (Option Bool) Bool := fun _ _ => do
  let a ← ProbOracleComp.query (spec := Ports) (.inr (some true))
  let b ← ProbOracleComp.query (spec := Ports) (.inr (some false))
  let u ← ProbOracleComp.query (spec := Ports) (.inl (0,()))
  let v ← ProbOracleComp.query (spec := Ports) (.inr none)
  return a && b && (decide (u = some true) || v)

abbrev parent := Test.parent true

@[expose] def port : WordPort (Option Bool) Bool :=
  ⟨encOption encBool, Decoder.option Decoder.bool, encBool, Decoder.bool⟩

private def memoryCodec : WordCodec Bool := ⟨encBool, Decoder.bool.decode, Decoder.bool.decode_enc⟩

private theorem set_ppt : ComputableInPolyTime set encBool net.query :=
  (ComputableInPolyTime.sumInr Test.party.query
    (WordPort.sum Test.raw Child.network).query).comp
      ((ComputableInPolyTime.sumInr Test.raw.query Child.network.query).comp
        (ComputableInPolyTime.sumInr Child.party.query encBool))

private theorem ack_ppt : ComputableInPolyTime ack net.reply encBool := by
  let last := ComputableInPolyTime.sumElim
    (ComputableInPolyTime.const (encIn := Child.party.reply) (encOut := encBool) false)
    (ComputableInPolyTime.id' (encIn := encBool))
  let mid := ComputableInPolyTime.sumElim
    (ComputableInPolyTime.const (encIn := Test.raw.reply) (encOut := encBool) false) last
  exact (ComputableInPolyTime.sumElim
    (ComputableInPolyTime.const (encIn := Test.party.reply) (encOut := encBool) false)
    mid).of_enc_eq (fun r => by rcases r with _ | (_ | (_ | _)) <;> rfl)

/-- Issue one request and read its bounded reply. Set uses the old saved bit to select the
request and its acknowledgment to update memory. Fetch preserves memory on every reply. -/
theorem adv_ppt : adv.IsPPT net port := by
  let T := PPTParam 1 × (Unit × Word) × Word
  let E := encHandlerCall (encPPTParam 1) (encFinite Unit) encBits
  let cmd := fun x : T => port.queryDecoder.decode x.2.1.2
  let saved := fun x : T => Decoder.bool.decode x.2.2
  have hc : ComputableInPolyTime cmd E (encFinite (Option Bool)) :=
    (ComputableInPolyTime.of_finite id (encIn := port.query)
      (encOut := encFinite (Option Bool))).comp
      (port.queryDecoder.computableInPolyTime.comp (by unfold E T encHandlerCall; fun_prop))
  have hs : ComputableInPolyTime saved E encBool := Decoder.bool.computableInPolyTime.comp
    (by unfold E T encHandlerCall; fun_prop)
  have hb : ComputableInPolyTime (fun x : T => x.1.replyBound) E encUnary := by
    unfold E T encHandlerCall; fun_prop
  let get (q : T → Test.OQ) (x : T) :=
    net.replyDecoder.decode <$> (List.take x.1.replyBound <$>
      ProbOracleComp.query (spec := fun _ : Unit × Word => Word) ((), net.query (q x)))
  have receive (q : T → Test.OQ) (hp : ComputableInPolyTime q E net.query) :
      IsOraclePPTOn E net.reply (get q) :=
    (IsOraclePPTOn.query_take () hp.encoding_comp hb).map net.replyDecoder.computableInPolyTime
  let branch : Option Bool → T → WordOracleComp Unit (Word × Word)
    | some c => fun x => (fun r => (encBool (ack r), encBool (c && ack r))) <$>
        get (fun a => set (saved a)) x
    | none => fun x => (fun r => (encBool (Test.readNet true r), encBool (saved x))) <$>
        get (fun _ => readRoute) x
  have impl := IsOraclePPTOn.finite_cases (branch := branch) hc (by
    rintro (_ | c)
    · exact (receive (fun _ => readRoute) (.const readRoute)).map_with
        ((((Test.readNet_ppt true).comp (ComputableInPolyTime.snd E net.reply)).encoding_comp).prod
          ((hs.comp (ComputableInPolyTime.fst E net.reply)).encoding_comp))
    · exact (receive _ (set_ppt.comp hs)).map
        (ack_ppt.encoding_comp.prod
          ((ComputableInPolyTime.bool_and' (ComputableInPolyTime.const c) ack_ppt).encoding_comp)))
  refine ⟨{ codec := fun _ _ => memoryCodec
            init := (ComputableInPolyTime.const (encIn := encPPTParam 1) (encOut := encBits)
              (encBool false)).isPPTOn
            normalize := Decoder.bool.computableInPolyTime.encoding_comp.comp
              (ComputableInPolyTime.snd (encPPTParam 1) encBits)
            growth _ _ := 0
            growth_poly := PolyBounded.const 0
            handle := ?_
            preserve := ?_ }⟩
  · refine impl.congr fun x σ o t => ?_
    apply congrArg (fun prog => ProbOracleComp.runWith o prog t)
    change branch (cmd x) x =
      (fun r : Bool × Bool => (encBool r.1, encBool r.2)) <$>
        ProbOracleComp.lowerWith (WordInterface.net net) x.1.replyBound
          ((match cmd x with
            | some c => fun s => (fun r => (ack r, c && ack r)) <$>
                ProbOracleComp.query (spec := netSpec Test.OQ ORsp) (set s)
            | none => fun s => (fun r => (Test.readNet true r, s)) <$>
                ProbOracleComp.query (spec := netSpec Test.OQ ORsp) readRoute) (saved x))
    cases cmd x <;> rfl
  · intro p q s out hout
    obtain ⟨_,_,rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hout
    rfl

private abbrev wire := WordInterface.exec party port

theorem test_ppt : test.IsPPT party port := by
  have hb : ComputableInPolyTime EnvParam.replyBound encEnvParam encUnary := by fun_prop
  let get (q : (Fin 1 × Unit) ⊕ Option Bool) (e : EnvParam) :=
    ProbOracleComp.lowerWith wire e.replyBound (ProbOracleComp.query (spec := Ports) q)
  have getPPT (q : (Fin 1 × Unit) ⊕ Option Bool) :
      IsOraclePPTOn (Operation := wire.Channel) encEnvParam (wire.reply q) (get q) :=
    wire.isOraclePPTOn_lowerWith_query (query := fun _ : EnvParam => q)
      (limit := EnvParam.replyBound) (.const _) (.const _) hb
  have read := (getPPT (.inl (0,()))).map
    (show ComputableInPolyTime (fun r => decide (r = some true)) party.reply encBool from
      ComputableInPolyTime.id'.decide_eq' (.const (some true)))
  have cmds := Test.combine Bool.and (getPPT (.inr (some true))) (getPPT (.inr (some false)))
  have views := Test.combine Bool.or read (getPPT (.inr none))
  apply (Test.combine Bool.and cmds views).congr
  intro e σ oracle s
  apply congrArg (fun prog => ProbOracleComp.runWith oracle prog s)
  simp [get, test, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_pure, ProbOracleComp.simulate_query, map_eq_bind_pure_comp, bind_assoc]

abbrev innerTester (C : Finset (Fin 1)) := Computational.innerTester parent C adv test
abbrev command (c : Bool) : (Fin 1 × Word) ⊕ Child.Q := .inr (.inr c)
abbrev ok (r : Child.R) := ack (.inr (.inr r))

theorem inner_honest (κ : ℕ) (z : Word) :
    innerTester ∅ κ z = (do
      let a ← ProbOracleComp.query (spec := Test.subPorts) (command false)
      let b ← ProbOracleComp.query (spec := Test.subPorts) (command (true && ok a))
      let p ← ProbOracleComp.query (spec := Test.subPorts) ordinary
      let v ← ProbOracleComp.query (spec := Test.subPorts) routed
      return ok a && ok b && (decide (some (Test.observe true p) = some true) ||
        Test.readNet true (.inr (.inr v)))) := rfl

theorem inner_corrupt (κ : ℕ) (z : Word) :
    innerTester {0} κ z = (do
      let a ← ProbOracleComp.query (spec := Test.subPorts) (command false)
      let b ← ProbOracleComp.query (spec := Test.subPorts) (command (true && ok a))
      let v ← ProbOracleComp.query (spec := Test.subPorts) routed
      return ok a && ok b && (decide ((none : Option Bool) = some true) ||
        Test.readNet true (.inr (.inr v)))) := rfl

private theorem service_cut (C : Finset (Fin 1)) :
    Experiment.ServiceCut Experiment.dummy C (innerTester C) := by
  refine ⟨fun e => e.replyBound + 5, by fun_prop, ?_⟩
  intro e σ o t state _
  simp only [absorbAdversary, Experiment.dummy, dummyAdversary, Machine.liftRight_id,
    Machine.link_id]
  rcases Test.cases_set C with rfl | rfl <;> first | rw [inner_honest] | rw [inner_corrupt]
  -- Each query is a setting, the ordinary read, or the routed read. The same cap
  -- applies at every successor state of the service and the external oracle.
  all_goals
    repeat'
      apply RepliesFitOn.query
      · apply Test.step_bound
        first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
      intro reply _
    exact .pure _ _ _

theorem admitted (C : Finset (Fin 1)) :
    (Application.source parent party raw port).Tests party port adv C test := by
  refine ⟨test_ppt, ?_, ?_, service_cut C⟩
  · change Computational.ReplyCap (fun k set => liftAdversary (adv k set))
      (WordInterface.exec party net) party port C test
    apply Computational.ReplyCap.of_global
    have h : Machine.IsReplyBounded adv (WordInterface.net net) (WordInterface.net port) :=
      ⟨fun _ => 1, PolyBounded.const 1, fun _ _ _ _ _ => le_rfl⟩
    exact h.liftRight
  · change Computational.ReplyCap (fun k set => routeCorrupt set (hybridWrap (parent k set)))
      (WordInterface.exec Child.party Child.network) party net C (absorbAdversary C adv test)
    apply Computational.ReplyCap.of_global
    exact ((Test.parent_bounded true).hybridWrap (nq := Child.network)).routeCorrupt

theorem close_test (G : Primitive.GeneratorFamily) (hG : G.Secure IsPPTBitStringTest)
    (C : Finset (Fin 1)) :
    Computational.Close (exec (compose parent (Application.real G)) adv C test)
      (exec (compose parent Application.ideal) sim C test) :=
  (Application.witness parent party raw port (Test.parent_ppt true)
    G hG adv ⟨adv_ppt,trivial⟩).close C test (admitted C)

/-- The additional setting command changes the wire trace. After both acknowledgments,
the child holds exactly the final setting used in the forwarding fixture. -/
theorem open_trace (inv : Bool) (C : Finset (Fin 1)) (κ : ℕ) (z : Word) :
    (Test.wrapped inv C κ).link (innerTester C κ z) =
      (Test.decision inv true) <$> ProbOracleComp.query (spec := Primitive.SamplePort) () := by
  rw [← Test.open_trace inv true C κ z]
  rcases Test.cases_set C with rfl | rfl <;> cases inv <;> rfl

/-- The stateful full execution on an arbitrary private draw. The tester observes the tag and
the first challenge bit, including when the adversary receives the only successful read. -/
theorem full_trace (inv : Bool) (draw : Computational.Sampler) (C : Finset (Fin 1))
    (κ : ℕ) (z : Word) :
    exec (compose parent (Child.protocol inv draw)) adv C test κ z =
      Test.decision inv true <$> draw κ := by
  rw [exec_eq_exec_dummy (compose parent _) adv, exec_compose_dummy,
    Child.protocol, HybridFunctionality.exec_close, Primitive.resource_run]
  simp only [absorbAdversary, dummyAdversary, Machine.liftRight_id, Machine.link_id]
  change (draw κ >>= fun w =>
    Primitive.answer ((Test.wrapped inv C κ).link (innerTester C κ z)) w) = _
  rw [open_trace]
  simp [Primitive.answer, map_eq_bind_pure_comp]

theorem full_law (inv : Bool) (draw aux : Computational.Sampler) (C : Finset (Fin 1))
    (κ : ℕ) :
    Computational.sampled (exec (compose parent (Child.protocol inv draw)) adv C test) aux κ =
      (Test.decision inv true <$> draw κ).eval := by
  simp only [Computational.sampled, full_trace, PMF.bind_const]

theorem translated_law (draw aux : Computational.Sampler) (C : Finset (Fin 1)) (κ : ℕ) :
    Computational.sampled (exec (compose parent (Child.protocol true draw)) sim C test) aux κ =
      (Test.decision false true <$> draw κ).eval := by
  rw [← Application.translation_full parent draw aux adv C test κ, full_law]

/-- The second setting command uses cleared memory. Every other activation runs normally. -/
def resetOnSecond : Adv := fun κ C => { (adv κ C) with
  handle q s := ((adv κ C).handle q).run (if q = some false then false else s) }

/-- For the same challenge and tester, erasing the acknowledged first bit before the second
setting changes the external decision on either route. -/
theorem detectsReset (C : Finset (Fin 1)) (κ : ℕ) (z : Word) :
    let π := compose parent (Child.protocol false (fun _ => pure [false]))
    exec π adv C test κ z = pure true ∧ exec π resetOnSecond C test κ z = pure false := by
  dsimp only
  constructor
  · rw [full_trace]
    rfl
  · rw [exec_eq_exec_dummy (compose parent _) resetOnSecond, exec_compose_dummy,
      Child.protocol, HybridFunctionality.exec_close, Primitive.resource_run]
    simp only [absorbAdversary, dummyAdversary, Machine.liftRight_id, Machine.link_id]
    let tester := Computational.innerTester parent C resetOnSecond test
    change Primitive.answer ((Test.wrapped false C κ).link (tester κ z)) [false] = _
    have h : (Test.wrapped false C κ).link (tester κ z) =
        (Test.wrapped true C κ).link (Test.T true C κ z) := by
      rcases Test.cases_set C with rfl | rfl <;> rfl
    rw [h, Test.open_trace]
    rfl

/-- With the same one-bit private word, forwarding the two setting commands verbatim gives
advantage one for the actual admitted tester. The outer adversary keeps its normal memory. -/
theorem forward_only_gap (aux : Computational.Sampler) (C : Finset (Fin 1)) (κ : ℕ) :
    let draw : Computational.Sampler := fun _ => pure [false]
    Game.advantage (Computational.sampled (exec (compose parent (Child.protocol false draw))
      adv C test) aux κ) (Computational.sampled (exec (compose parent (Child.protocol true draw))
      (compSim (hybridSim Experiment.dummy) adv) C test) aux κ) = 1 := by
  dsimp only
  rw [Application.forwarding_full, full_law, full_law]
  simp [Test.decision, Game.succProbability]

/-- Keeping the translator, the admitted stateful tester distinguishes the zero generator
from a uniform two-bit challenge with advantage one half at parameter one on either route. -/
theorem combined_gap (aux : Computational.Sampler) (C : Finset (Fin 1)) :
    Game.advantage (Computational.sampled (exec (compose parent
      (Application.real Test.zeroGenerator)) adv C test) aux 1)
      (Computational.sampled (exec (compose parent Application.ideal) sim C test) aux 1) =
        1 / 2 := by
  rw [full_law, translated_law]
  simpa only [Test.full_law, Test.translated_law] using Test.combined_gap aux C

end CslibFrontierTests.Crypto.UCComputational.Stateful
