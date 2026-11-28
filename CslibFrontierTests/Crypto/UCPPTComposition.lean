/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Protocols.UC.PPT.Composition
public import CslibFrontier.Crypto.Protocols.UC.PPT.Execution
public import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Languages.Probabilistic.Oracle.Support

/-!
# Two calls to a strict-PPT composed simulator

The outer adversary submits its saved bit and retains the current request on acknowledgment.
The inner simulator complements each submitted bit. Both the strict-PPT result and the trace
below use the literal `compSim` from UC. The first network acknowledgment controls the second
network request. The second acknowledgment controls the state for a subsequent activation.

A second simulator installs a uniform κ-bit key and later reads its first bit. Its unpadded state
grows on install. A polynomial state capacity certifies it against every strict-PPT caller.
-/

namespace CslibFrontierTests.Crypto.UCPPTComposition

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

/-- Commands and acknowledgments use one bit each. -/
@[expose] public def bitPort : WordPort Bool Bool := ⟨encBool, Decoder.bool, encBool, Decoder.bool⟩

/-- One-bit machine specified by its network command and its update on acknowledgment. -/
@[expose] public def bitMachine (send : Bool × Bool → Bool) (save : (Bool × Bool) × Bool → Bool) :
    Adversary 1 Bool Bool Bool Bool := fun _ _ => {
  State := Bool
  init := pure false
  handle q s := (fun ack => (ack, save ((q, s), ack))) <$>
    ProbOracleComp.query (spec := netSpec Bool Bool) (send (q, s)) }

private def bitCodec (send save) : StateCodec (bitMachine send save) := fun _ _ =>
  ⟨encBool, Decoder.bool.decode, Decoder.bool.decode_enc⟩

private noncomputable def bitCertificate (send save) :
    PPTCertificate (bitMachine send save)
      (WordInterface.net bitPort) (WordInterface.net bitPort) := by
  let T := PPTParam 1 × (Unit × List Bool) × List Bool
  let E := encHandlerCall (encPPTParam 1) (encFinite Unit) encBits
  let pre := fun x : T => (Decoder.bool.decode x.2.1.2, Decoder.bool.decode x.2.2)
  let B := encPair encBool encBool
  have hp : ComputableInPolyTime pre E B := by
    apply ComputableInPolyTime.prod
    all_goals apply Decoder.bool.computableInPolyTime.comp
    all_goals unfold T E encHandlerCall; fun_prop
  have hb : ComputableInPolyTime (fun x : T => x.1.replyBound) E encUnary := by
    unfold T E encHandlerCall; fun_prop
  have hsend := ComputableInPolyTime.of_finite send (encIn := B) (encOut := encBool)
  have hsave := ComputableInPolyTime.of_finite save (encIn := encPair B encBool) (encOut := encBool)
  have hquery := (IsOraclePPTOn.query_take () (hsend.comp hp).encoding_comp hb).map
    Decoder.bool.computableInPolyTime
  have hreturned := ComputableInPolyTime.snd E encBool
  have hnext := hsave.comp ((hp.comp (ComputableInPolyTime.fst E encBool)).prod hreturned)
  have impl := hquery.map_with (f := fun x ack => (encBool ack, encBool (save (pre x, ack))))
    (hreturned.encoding_comp.prod hnext.encoding_comp)
  refine { codec := bitCodec send save
           init := (ComputableInPolyTime.const (encIn := encPPTParam 1) (encOut := encBits)
             (encBool false)).isPPTOn
           normalize := Decoder.bool.computableInPolyTime.encoding_comp.comp
             (ComputableInPolyTime.snd (encPPTParam 1) encBits)
           handle := ?_
           growth _ _ := 0
           growth_poly := PolyBounded.const 0
           preserve := ?_ }
  · refine impl.congr fun x σ o t => ?_
    apply congrArg (fun prog => ProbOracleComp.runWith o prog t)
    simp [wordHandle, bitMachine, bitCodec, bitPort, pre, StateT.run, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_query, WordInterface.lowerQuery, WordInterface.net, Functor.map_map]
    rfl
  · intro p rq s v hv
    obtain ⟨_, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hv
    rfl

/-- Send the saved bit and retain the latest request on acknowledgment. -/
public abbrev outer := bitMachine Prod.snd (fun ((q, _), ack) => q && ack)

/-- Complement the received command and remember its original value. -/
public abbrev relay := bitMachine (fun (q, _) => !q) (fun ((q, _), _) => q)

/-- The command-translating simulator composed with the stateful adversary is strict PPT. -/
public theorem compSim_isPPT : (compSim relay outer).IsPPT bitPort bitPort := by
  apply PPTCertificate.isPPT_comp_of_computableCap_nongrowing
    (A := outer) (D := relay) (bitCertificate _ _) (bitCertificate _ _) (fun _ => 1)
  · exact ComputableInPolyTime.const 1
  · intro _ _ _ _ _; exact le_rfl
  · intro _ _ _ _ _; exact le_rfl

/-- Submit two adversary requests in order, retaining both responses. -/
@[expose] public def twoCalls (q₁ q₂ : Bool) :
    ProbOracleComp (netSpec Bool Bool) (Bool × Bool) := do
  let a ← ProbOracleComp.query (spec := netSpec Bool Bool) q₁
  let b ← ProbOracleComp.query (spec := netSpec Bool Bool) q₂
  return (a, b)

/-- The first acknowledgment controls the second network request when the first input is true.
The result records both acknowledgments and the two persistent states. -/
public theorem compSim_twoCalls (κ : ℕ) (C : Finset (Fin 1)) (q₁ q₂ : Bool) :
    ((compSim relay outer) κ C).runFrom (twoCalls q₁ q₂) (false, false) =
      (do let a ← ProbOracleComp.query (spec := netSpec Bool Bool) true
          let b ← ProbOracleComp.query (spec := netSpec Bool Bool) (!(q₁ && a))
          return ((a, b), (q₂ && b, q₁ && a))) := by
  rfl

/-! ### A key allocated on one activation and read on the next -/

/-- Draw new key material only on install and return an observation of the selected key. -/
@[expose] public noncomputable def keyStep (κ : ℕ) (install : Bool) (saved : List Bool) :
    ProbComp (Bool × List Bool) :=
  (fun fresh =>
    let key := if install then fresh else saved
    (key.headD false, key)) <$> BitString.sampleList (if install then κ else 0)

/-- Install samples a fresh uniform key of length κ. Read returns its first bit, or false if empty.
Both commands return one bit, and the state encoding stores the actual key word. -/
@[expose] public noncomputable def keyRelay : Adversary 1 Bool Bool Bool Bool := fun κ _ => {
  State := List Bool
  init := pure []
  handle q s := ProbOracleComp.sample (keyStep κ q s) }

private def keyCodec : StateCodec keyRelay := fun _ _ => ⟨encBits, id, fun _ => rfl⟩

private theorem keyStep_size (κ : ℕ) (q : Bool) (s : List Bool) (v : Bool × List Bool)
    (hv : v ∈ (keyStep κ q s).eval.support) : v.2.length ≤ max κ s.length := by
  rw [keyStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [BitString.eval_sampleList] at hw
  have len := BitString.length_of_mem_support_uniformList hw
  cases q <;> simp_all

private noncomputable def keyCertificate :
    PPTCertificate keyRelay (WordInterface.net bitPort) (WordInterface.net bitPort) := by
  let T := PPTParam 1 × (Unit × List Bool) × List Bool
  let E := encHandlerCall (encPPTParam 1) (encFinite Unit) encBits
  let install := fun x : T => Decoder.bool.decode x.2.1.2
  have qi : ComputableInPolyTime install E encBool := by
    apply Decoder.bool.computableInPolyTime.comp
    unfold T E encHandlerCall; fun_prop
  have sec : ComputableInPolyTime (fun x : T => x.1.secParam) E encUnary := by
    unfold T E encHandlerCall; fun_prop
  have old : ComputableInPolyTime (fun x : T => x.2.2) E encBits := by
    unfold T E encHandlerCall; fun_prop
  have count := qi.ite' sec (ComputableInPolyTime.const (encOut := encUnary) 0)
  let input := ComputableInPolyTime.fst E encBits
  let fresh := ComputableInPolyTime.snd E encBits
  have kept := (qi.comp input).ite' fresh (old.comp input)
  have head := ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false
  have impl := IsPPTOn.of_seeded count (((head.comp kept).encoding_comp).prod kept)
  refine { codec := keyCodec
           init := (ComputableInPolyTime.const (encIn := encPPTParam 1) (encOut := encBits)
             ([] : List Bool)).isPPTOn
           normalize := ComputableInPolyTime.snd (encPPTParam 1) encBits
           handle := ?_
           growth p _ := p.secParam
           growth_poly := ?_
           preserve := ?_ }
  · refine impl.isOraclePPTOn.congr fun x σ o t => ?_
    apply congrArg (fun prog => ProbOracleComp.runWith o prog t)
    simp only [wordHandle, keyRelay, keyStep, keyCodec, StateT.run, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_sample, ← ProbOracleComp.sample_map, Functor.map_map]
    rfl
  · simpa only [encUnary_apply, List.length_replicate] using
      (show ComputableInPolyTime (fun x : PPTParam 1 × List Bool => x.1.secParam)
        (encPair (encPPTParam 1) encBits) encUnary by fun_prop).polyBounded_length
  · intro p req s r hr
    obtain ⟨v, hv, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hr
    simp only [keyRelay, StateT.run, keyCodec, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_sample,
      ProbOracleComp.support_sample] at hv
    have bound := keyStep_size _ _ _ _ hv
    change v.2.length ≤ max p.secParam s.length at bound
    change v.2.length ≤ s.length + p.secParam
    omega

/-- Install and read each return exactly one encoded bit. -/
public theorem keyRelay_replyBounded :
    Machine.IsReplyBounded keyRelay (WordInterface.net bitPort) (WordInterface.net bitPort) :=
  ⟨fun _ => 1, PolyBounded.const 1, fun _ _ _ _ _ => le_rfl⟩

/-- Any strict-PPT caller can use the key simulator with its natural variable-length state. -/
public theorem keyRelay_comp_isPPT {Q R : Type} (control : WordPort Q R)
    {A : Adversary 1 Q R Bool Bool} (hA : A.IsPPT bitPort control) :
    (compSim keyRelay A).IsPPT bitPort control := by
  obtain ⟨a⟩ := hA
  apply PPTCertificate.isPPT_comp_of_replyBounded_boundedState a keyCertificate
    keyRelay_replyBounded PPTParam.secParam
  · simpa only [encUnary_apply, List.length_replicate] using
      (show ComputableInPolyTime (PPTParam.secParam : PPTParam 1 → ℕ)
        (encPPTParam 1) encUnary by fun_prop).polyBounded_length
  · intro p q s v hv
    simp only [keyRelay, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_sample,
      ProbOracleComp.support_sample] at hv
    exact keyStep_size _ _ _ _ hv

/-- A tester can absorb the actual composed adversary when the outer caller bounds its replies. -/
public theorem absorbKeyRelay_isPPT {In Out Q R : Type}
    {party : WordPort (Fin 1 × In) (Option Out)} {control : WordPort Q R}
    {A : Adversary 1 Q R Bool Bool} {Z : Environment 1 In Out Q R}
    (hz : Z.IsPPT party control) (ha : A.IsPPT bitPort control)
    (bound : Machine.IsReplyBounded A (WordInterface.net bitPort) (WordInterface.net control))
    (C : Finset (Fin 1)) :
    (absorbAdversary C (compSim keyRelay A) Z).IsPPT party bitPort :=
  hz.absorbAdversary (keyRelay_comp_isPPT control ha) (bound.comp keyRelay_replyBounded) C

/-- On the unpadded encoding, a supported install violates per-call non-growth already at κ = 1. -/
public theorem keyRelay_allocates :
    ¬ ∀ v ∈ OracleComp.support (ProbOracleComp.lowerWith (WordInterface.net bitPort) 0
      (((keyRelay 1 ∅).handle true).run [])), v.2.length ≤ ([] : List Bool).length := by
  intro h
  have growing := h (true, [true]) (by
    simp only [keyRelay, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_sample,
      ProbOracleComp.support_sample, keyStep, ite_true, ProbComp.eval_map,
      BitString.eval_sampleList]
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨[true], BitString.mem_support_uniformList_iff.mpr rfl, rfl⟩)
  exact Nat.not_succ_le_zero 0 growing

private theorem forward_key_handle (κ : ℕ) (C : Finset (Fin 1)) (q : Bool)
    (s : (keyRelay κ C).State) :
    (((compSim keyRelay (dummyAdversary 1 Bool Bool) κ C).handle q).run (PUnit.unit, s)) =
      (fun v => (v.1, (PUnit.unit, v.2))) <$> ProbOracleComp.sample (keyStep κ q s) := by
  change Equiv.prodAssoc _ _ _ <$> (keyRelay κ C).runFrom
    ((fun r => (r, PUnit.unit)) <$> ProbOracleComp.query (spec := netSpec Bool Bool) q) s = _
  erw [Machine.runFrom_map, Machine.runFrom_query, Functor.map_map]
  rfl

/-- Install and then read through the actual composite. Both replies expose the same sampled bit. -/
public theorem keyRelay_twoCalls (κ : ℕ) (C : Finset (Fin 1)) :
    (compSim keyRelay (dummyAdversary 1 Bool Bool) κ C).runFrom
      (twoCalls true false) (PUnit.unit, []) =
      (fun key : List Bool => ((key.headD false, key.headD false), (PUnit.unit, key))) <$>
        ProbOracleComp.sample (spec := netSpec Bool Bool) (BitString.sampleList κ) := by
  unfold twoCalls
  erw [Machine.runFrom_bind, Machine.runFrom_query, forward_key_handle]
  simp only [keyStep, ↓reduceIte, ProbOracleComp.sample_map, Functor.map_map,
    bind_pure_comp, Machine.runFrom_map, Machine.runFrom_query]
  erw [bind_map_left]
  conv_rhs => rw [map_eq_pure_bind]
  apply bind_congr
  intro key
  erw [forward_key_handle]
  simp [keyStep, BitString.sampleList]
  rfl

/-- The caller can see a true second reply at κ = 1. Resetting the simulator before the read
removes that event, even when the caller observes only the read reply. -/
public theorem keyRelay_detectsReset (C : Finset (Fin 1)) :
    true ∈ OracleComp.support ((fun v => v.1.2) <$>
      (compSim keyRelay (dummyAdversary 1 Bool Bool) 1 C).runFrom
        (twoCalls true false) (PUnit.unit, [])) ∧
    true ∉ OracleComp.support (Prod.fst <$>
      (compSim keyRelay (dummyAdversary 1 Bool Bool) 1 C).runFrom
        (ProbOracleComp.query (spec := netSpec Bool Bool) false) (PUnit.unit, [])) := by
  constructor
  · rw [keyRelay_twoCalls]
    apply OracleComp.mem_supportWith_map_iff.mpr
    refine ⟨((true, true), (PUnit.unit, [true])), ?_, rfl⟩
    apply OracleComp.mem_supportWith_map_iff.mpr
    refine ⟨[true], ?_, rfl⟩
    change [true] ∈ OracleComp.support
      (ProbOracleComp.sample (spec := netSpec Bool Bool) (BitString.sampleList 1))
    rw [ProbOracleComp.support_sample, BitString.eval_sampleList]
    exact BitString.mem_support_uniformList_iff.mpr rfl
  · erw [Machine.runFrom_query, forward_key_handle]
    change true ∉ OracleComp.support (pure false : ProbOracleComp (netSpec Bool Bool) Bool)
    simp

end CslibFrontierTests.Crypto.UCPPTComposition
