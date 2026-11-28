/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Probabilistic.Oracle.RunState
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Crypto.Protocols.UC.Computational
public import CslibFrontier.Crypto.Protocols.UC.HybridFunctionality
public import CslibFrontier.Crypto.Protocols.UC.PPT.Link
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
import CslibFrontier.Computability.Probabilistic.PPT.Capture

/-!
# A one-sample PRG distinguisher for a linked UC tester

The primitive challenger supplies one word. The distinguisher samples independent auxiliary
input and runs the linked UC context, answering its private sample port with that word.
`wordTest_isPPT` certifies the implementation on the unary parameter and the full challenge.
-/

public section

namespace CslibFrontierTests.Crypto.UCComputational.Primitive

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

abbrev SamplePort : Unit → Type := fun _ => List Bool

/-- An independent word is sampled at initialization and retained across calls. -/
abbrev resource (draw : ProbComp (List Bool)) : Machine OracleSpec.empty SamplePort where
  State := List Bool
  init := draw
  handle _ w := pure (w, w)

@[expose] def answer {α : Type} (K : ProbOracleComp SamplePort α) (r : List Bool) : ProbComp α :=
  OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin (fun _ => pure r)) K

@[expose] def wordTest (K : ℕ → List Bool → ProbOracleComp SamplePort Bool)
    (sampler : ℕ → ProbComp (List Bool)) (κ : ℕ) (r : List Bool) : ProbComp Bool := do
  let z ← sampler κ
  answer (K κ z) r

@[expose] noncomputable def sampleTest (K : ℕ → List Bool → ProbOracleComp SamplePort Bool)
    (sampler : ℕ → ProbComp (List Bool)) (κ : ℕ) : PRG.Adversary (Fin (2 * κ) → Bool) :=
  fun r => (wordTest K sampler κ (List.ofFn r)).eval

private theorem resource_runFrom {α : Type} (draw : ProbComp (List Bool))
    (K : ProbOracleComp SamplePort α) (r : List Bool) :
    (resource draw).runFrom K r =
      (fun a => (a, r)) <$> ProbOracleComp.sample (answer K r) := by
  induction K using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    rw [Machine.runFrom_bind, Machine.runFrom_call]
    simp only [answer, OracleComp.interpret_bind, OracleComp.interpret_query,
      ProbOracleComp.sample_bind, map_bind]
    cases q with
    | inl k =>
      simp only [Machine.handler, OracleComp.sumHandler, StateT.run_lift, bind_assoc, pure_bind]
      exact congrArg (fun f => ProbOracleComp.sample (ProbComp.unifFin k) >>= f) (funext ih)
    | inr u =>
      simp only [Machine.handler, OracleComp.sumHandler, resource, StateT.run,
        ProbOracleComp.sample_pure, pure_bind]
      exact ih r

theorem resource_run {α : Type} (draw : ProbComp (List Bool)) (K : ProbOracleComp SamplePort α) :
    (resource draw).run K = (draw >>= fun r => answer K r) := by
  simp only [Machine.run, Machine.link, Machine.closeProgram_bind, Machine.closeProgram_sample]
  apply congrArg (fun f => draw >>= f)
  funext r
  rw [resource_runFrom, Functor.map_map]
  simp

abbrev GeneratorFamily := PRG.Family (fun κ => Fin κ → Bool) (fun κ => Fin (2 * κ) → Bool)

@[expose] noncomputable def generated (G : GeneratorFamily) (κ : ℕ) : ProbComp (List Bool) :=
  (fun s => List.ofFn (G κ (BitString.ofList κ s))) <$> BitString.sampleList κ

@[expose] noncomputable def uniformOutput (κ : ℕ) : ProbComp (List Bool) :=
  BitString.sampleList (2 * κ)

theorem generated_eval (G : GeneratorFamily) (κ : ℕ) :
    (generated G κ).eval = (G κ).outputDist.map List.ofFn := by
  simp [generated, PRG.Generator.outputDist, BitString.uniformList, PMF.map_comp, Function.comp_def]

@[expose] def sampleUnitDecoder : Decoder encUnit where
  decode _ := ()
  decode_enc _ := rfl
  computable := (ComputableInPolyTime.const (encIn := encBits) (encOut := encUnit) ()).exists_degree

/-- The resource has one operation and returns raw bits without framing. -/
@[expose] def sampleWire : WordInterface SamplePort :=
  WordInterface.net
    (⟨encUnit, sampleUnitDecoder, encBits, Decoder.bits⟩ : WordPort Unit (List Bool))

/-- An open caller compiled uniformly in the security parameter, imported reply cap and aux. -/
@[expose] def PackedPPT (K : ℕ → List Bool → ProbOracleComp SamplePort Bool) : Prop :=
  IsOraclePPTOn encEnvParam encBool (fun e : EnvParam =>
    ProbOracleComp.lowerWith sampleWire e.replyBound (K e.secParam e.aux))

private theorem run_lower_fixed (K : ProbOracleComp SamplePort Bool) (r : List Bool) :
    ((K.lowerWith sampleWire r.length).run (fun _ => pure r)) = answer K r := by
  rw [ProbOracleComp.lowerWith, ProbOracleComp.run_simulate]
  change K.run _ = K.run (fun _ => pure r)
  apply congrArg K.run
  funext q
  unfold WordInterface.lowerQuery
  rw [ProbOracleComp.run_map, ProbOracleComp.run_map, ProbOracleComp.run_query]
  simp [sampleWire, WordInterface.net, Decoder.bits]

/-- Close the last port with the challenge supplied as actual input. The executable reads
its length, prepares the original caller parameters and pays for supplying the full word. -/
theorem wordTest_isPPT {K : ℕ → List Bool → ProbOracleComp SamplePort Bool}
    (hK : PackedPPT K) {sampler : ℕ → ProbComp (List Bool)}
    (hs : IsPPTOn encUnary encBits sampler) :
    IsPPTOn (encPair encUnary encBits) encBool
      (fun input : ℕ × List Bool => wordTest K sampler input.1 input.2) := by
  let inputEnc := encPair encUnary encBits
  let tripleEnc := encPair inputEnc encBits
  let prepare := fun a : (ℕ × List Bool) × List Bool =>
    (⟨a.1.1, a.1.2.length, a.2⟩ : EnvParam)
  have hword : ComputableInPolyTime (fun a : (ℕ × List Bool) × List Bool => a.1.2)
      tripleEnc encBits := by unfold tripleEnc inputEnc; fun_prop
  have hlen : ComputableInPolyTime (fun a : (ℕ × List Bool) × List Bool => a.1.2.length)
      tripleEnc encUnary := by
    simpa only [encBits_apply, Function.comp_def] using
      (ComputableInPolyTime.encoding_length encBits).comp hword
  have hp : ComputableInPolyTime prepare tripleEnc encEnvParam := by
    have hk : ComputableInPolyTime (fun a : (ℕ × List Bool) × List Bool => a.1.1)
        tripleEnc encUnary := by unfold tripleEnc inputEnc; fun_prop
    have hz := ComputableInPolyTime.snd inputEnc encBits
    unfold prepare
    fun_prop
  let O := fun (a : (ℕ × List Bool) × List Bool) (_ : sampleWire.Channel × List Bool) =>
    StateT.lift (σ := Unit) (pure a.1.2 : ProbComp (List Bool))
  let HEnc := encHandlerCall tripleEnc (encFinite sampleWire.Channel) encUnit
  have ho : IsPPTOn HEnc (encPair encBits encUnit)
      (fun p : ((ℕ × List Bool) × List Bool) × (sampleWire.Channel × List Bool) × Unit =>
        O p.1 p.2.1 p.2.2) := by
    have proj : ComputableInPolyTime
        (fun p : ((ℕ × List Bool) × List Bool) × (sampleWire.Channel × List Bool) × Unit => p.1)
        HEnc tripleEnc := by unfold HEnc encHandlerCall; fun_prop
    exact ((hword.comp proj).prod
      (ComputableInPolyTime.const (encIn := HEnc) (encOut := encUnit) ())).isPPTOn
  have hresources := hlen.comp (ComputableInPolyTime.fst tripleEnc encBits)
  have hrun := (show IsOraclePPTOn encEnvParam encBool _ from hK).isPPTOn_runState
    (oracle := O) (initial := fun _ => ()) (resources := fun a _ => a.1.2.length)
    hp ho (ComputableInPolyTime.const (encIn := tripleEnc) (encOut := encUnit) ())
    (fun _ _ => True) (fun _ => trivial) hresources (by
      intro a q s _ x hx
      change x ∈ (pure (a.1.2, s) : PMF (List Bool × Unit)).support at hx
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
      exact ⟨trivial, le_rfl, Nat.le_add_right _ _⟩)
  have hclosed : IsPPTOn tripleEnc encBool (fun a : (ℕ × List Bool) × List Bool =>
      answer (K a.1.1 a.2) a.1.2) := by
    refine (hrun.map (ComputableInPolyTime.fst encBool encUnit)).congr fun a => ?_
    dsimp only [O, prepare]
    rw [ProbOracleComp.runState_lift, run_lower_fixed]
    simp
  exact (hs.preprocess (ComputableInPolyTime.fst encUnary encBits)).bind_with hclosed

/-- The same word program realizes the finite test family in Frontier's uniform PRG game. -/
theorem sampleTest_admissible {K : ℕ → List Bool → ProbOracleComp SamplePort Bool}
    (hK : PackedPPT K) {sampler : ℕ → ProbComp (List Bool)}
    (hs : IsPPTOn encUnary encBits sampler) :
    IsPPTBitStringTest (sampleTest K sampler) :=
  ⟨wordTest K sampler, wordTest_isPPT hK hs, fun _ _ => rfl⟩

/-- The generated and uniform laws for any single private-word context. -/
theorem challenge_advantage (G : GeneratorFamily)
    (K : ℕ → List Bool → ProbOracleComp SamplePort Bool) (aux : Computational.Sampler) (κ : ℕ) :
    let test := fun r => (Primitive.wordTest K aux κ r).eval
    Game.advantage ((Primitive.generated G κ).eval.bind test)
      ((Primitive.uniformOutput κ).eval.bind test) =
    Game.advantage ((G κ).realExperiment (Primitive.sampleTest K aux κ))
      (PRG.Generator.idealExperiment (Primitive.sampleTest K aux κ)) := by
  dsimp only
  rw [Primitive.generated_eval, Primitive.uniformOutput,
    BitString.eval_sampleList, BitString.uniformList, PRG.Generator.realExperiment,
    PRG.Generator.idealExperiment, PMF.bind_map, PMF.bind_map]
  rfl

/-- The ordinary service reply consists of an option tag and a framed pair of words. -/
@[expose] def serviceParty : WordPort (Fin 1 × List Bool) (Option (List Bool × List Bool)) :=
  WordPort.party
    ⟨encBits, Decoder.bits, encPair encBits encBits, Decoder.pair Decoder.bits Decoder.bits⟩

variable {Q R : Type}

/-- Pack a one-party service with a private word port, retaining its own routed
handlers and state. Both caps quantify over the remaining external word oracle. -/
theorem packed_service {I O N B : Type} (H : HybridFunctionality 1 I O N B SamplePort)
    (party : WordPort (Fin 1 × I) (Option O)) (raw : WordPort N B) {ctl : WordPort Q R}
    {C : Finset (Fin 1)} {A : ExecAdversary 1 I O N B Q R} {Z : Environment 1 I O Q R}
    (hH : Machine.IsPPTFamily H.toMachine sampleWire (WordInterface.protocol party raw))
    (hA : A.IsPPT (WordPort.sum party raw) ctl) (hZ : Z.IsPPT party ctl)
    (capA : Computational.AdversaryCap party (WordPort.sum party raw) ctl A C Z)
    (capH : Computational.ReplyCap (fun k set => routeCorrupt set (H.toMachine k set))
      sampleWire party (WordPort.sum party raw) C (absorbAdversary C A Z)) :
    PackedPPT (fun k z => (routeCorrupt C (H.toMachine k C)).link (absorbAdversary C A Z k z)) := by
  obtain ⟨capA, polyA, reachA⟩ := capA
  obtain ⟨capF, polyF, reachF⟩ := capH
  have packedAZ : (absorbAdversary C A Z).IsPPT party (WordPort.sum party raw) :=
    hZ.link_of_reachable (hA.liftAdversary (party := party)) C capA polyA reachA
  have index : ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1)
      encBits (encFinite (Fin 1)) :=
    (ComputableInPolyTime.const (encIn := encBits) (encOut := encFinite (Fin 1))
      (0 : Fin 1)).of_enc_eq (fun _ => congrArg _ (Subsingleton.elim _ _))
  exact packedAZ.isOraclePPTOn_lowerWith_link_of_reachable (hH.routeCorrupt index)
    C capF polyF reachF

end CslibFrontierTests.Crypto.UCComputational.Primitive
