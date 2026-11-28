/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: local-only (test)

public import CslibFrontierTests.Crypto.UCComputational.Translator
import CslibFrontier.Computability.Probabilistic.PPT.Capture

/-!
# Computational one-child replacement from PRG security

A fixed private draw gives identical translated execution laws. Changing the draw gives
exactly the advantage of the primitive word distinguisher. The theorem `Application.witness`
then lifts the child witness through an arbitrary certified parent with the stated reachable
reply bounds, for each eligible outer adversary.
-/

public section

namespace CslibFrontierTests.Crypto.UCComputational.Experiment

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

open Child (Word Result service party raw network protocol relay)
open Primitive (SamplePort sampleWire GeneratorFamily generated uniformOutput)

abbrev Adv (U V : Type) := ExecAdversary 1 Word Result Bool Bool U V
abbrev Test (U V : Type) := Environment 1 Word Result U V
abbrev dummy := dummyAdversary 1 Child.Q Child.R

variable {U V : Type}

@[expose] def context (C : Finset (Fin 1)) (A : Adv U V) (Z : Test U V) (κ : ℕ) (z : Word) :
    ProbOracleComp SamplePort Bool :=
  (routeCorrupt C ((service false).toMachine κ C)).link (absorbAdversary C A Z κ z)

abbrev ServiceCut (A : Adv U V) (C : Finset (Fin 1)) (Z : Test U V) :=
  Computational.ReplyCap (fun k set => routeCorrupt set ((service false).toMachine k set))
    sampleWire party network C (absorbAdversary C A Z)

@[expose] def source (ctl : WordPort U V) : Computational.Profile 1 Word Result Bool Bool U V where
  network := network
  adversary _ := True
  tester A C Z := Computational.AdversaryCap party network ctl A C Z ∧ ServiceCut A C Z

@[expose] def target (U V : Type) : Computational.Profile 1 Word Result Bool Bool U V where
  network := network
  adversary _ := True
  tester _ _ _ := True

theorem dummy_eligible : (source network).Eligible network dummy :=
  ⟨Adversary.isPPT_dummyAdversary 1 network, trivial⟩

theorem dummy_cap (C : Finset (Fin 1)) (Z : Test Child.Q Child.R) :
    Computational.AdversaryCap party network network dummy C Z := by
  change Computational.ReplyCap (fun k set => liftAdversary (dummy k set))
    (WordInterface.exec party network) party network C Z
  apply Computational.ReplyCap.of_global
  simpa only [dummy, dummyAdversary, liftAdversary, Machine.liftRight_id] using
    (Machine.isReplyBounded_id (n := 1) (WordInterface.exec party network))

theorem sampled_eq (draw aux : Computational.Sampler) (A : Adv U V) (C : Finset (Fin 1))
    (Z : Test U V) (κ : ℕ) :
    Computational.sampled (exec (protocol false draw) A C Z) aux κ =
      (draw κ).eval.bind (fun r => (Primitive.wordTest (context C A Z) aux κ r).eval) := by
  simp only [Computational.sampled, protocol, HybridFunctionality.exec_close,
    Primitive.resource_run,
    ProbComp.eval_bind, context, Primitive.wordTest]
  exact PMF.bind_comm _ _ _

/-- Rewriting Set commands, with the private draw held fixed, incurs exactly zero loss. -/
theorem translate_sampled (draw aux : Computational.Sampler) (A : Adv U V) (C : Finset (Fin 1))
    (Z : Test U V) (κ : ℕ) :
    Computational.sampled (exec (protocol false draw) A C Z) aux κ =
      Computational.sampled (exec (protocol true draw) (compSim relay A) C Z) aux κ := by
  unfold Computational.sampled
  congr 1
  funext z
  exact Child.translation_with_adversary draw A C Z κ z

theorem translate_dummy (draw aux : Computational.Sampler) (C : Finset (Fin 1))
    (Z : Test Child.Q Child.R) (κ : ℕ) :
    Computational.sampled (exec (protocol false draw) dummy C Z) aux κ =
      Computational.sampled (exec (protocol true draw) relay C Z) aux κ := by
  unfold Computational.sampled
  congr 1
  funext z
  exact congrArg ProbComp.eval (Child.translation_exact draw C Z κ z)

theorem sampling_advantage (G : GeneratorFamily) (A : Adv U V) (C : Finset (Fin 1))
    (Z : Test U V) (aux : Computational.Sampler) (κ : ℕ) :
    let d := Primitive.sampleTest (context C A Z) aux κ
    Game.advantage (Computational.sampled (exec (protocol false (generated G)) A C Z) aux κ)
      (Computational.sampled (exec (protocol false uniformOutput) A C Z) aux κ) =
      Game.advantage ((G κ).realExperiment d) (PRG.Generator.idealExperiment d) := by
  rw [sampled_eq, sampled_eq]
  exact Primitive.challenge_advantage G _ aux κ

end CslibFrontierTests.Crypto.UCComputational.Experiment

namespace CslibFrontierTests.Crypto.UCComputational.Application

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

open Child (Word Result protocol relay)
open Primitive (generated uniformOutput GeneratorFamily)
open Experiment (dummy)

noncomputable abbrev real (G : GeneratorFamily) := protocol false (generated G)
noncomputable abbrev ideal := protocol true uniformOutput

section Child
variable {U V : Type} {ctl : WordPort U V}
    {A : Experiment.Adv U V} {C : Finset (Fin 1)} {Z : Experiment.Test U V}

theorem packed (ha : (Experiment.source ctl).Eligible ctl A)
    (hz : (Experiment.source ctl).Tests Child.party ctl A C Z) :
    Primitive.PackedPPT (Experiment.context C A Z) :=
  Primitive.packed_service (Child.service false) Child.party Child.raw
    (Child.service_ppt false) ha.1 hz.1 hz.2.1 hz.2.2

private theorem sample_close (G : GeneratorFamily) (secure : G.Secure IsPPTBitStringTest)
    (hK : Primitive.PackedPPT (Experiment.context C A Z)) :
    Computational.Close (exec (real G) A C Z) (exec (protocol false uniformOutput) A C Z) := by
  intro aux haux
  simp only [real, Experiment.sampling_advantage]
  exact (G.secure_iff_indistinguishable IsPPTBitStringTest).mp secure _
    (Primitive.sampleTest_admissible hK haux)

theorem child_witness (G : GeneratorFamily) (secure : G.Secure IsPPTBitStringTest)
    (A : Experiment.Adv U V) (ha : (Experiment.source ctl).Eligible ctl A) :
    Computational.Witness Child.party ctl (Experiment.source ctl)
      (Experiment.target U V) (real G) ideal A (compSim relay A) := by
  refine ⟨⟨Child.compSim_child_relay_ppt ctl A ha.1, trivial⟩, fun _ _ hz => ⟨hz.1, trivial⟩, ?_⟩
  intro C Z hz aux haux
  simpa only [ideal, ← Experiment.translate_sampled uniformOutput aux A C Z] using
    sample_close G secure (packed ha hz) aux haux

theorem child_emulates (G : GeneratorFamily) (secure : G.Secure IsPPTBitStringTest)
    (ctl : WordPort U V) :
    Computational.EmulatesOn Child.party ctl (Experiment.source ctl)
      (Experiment.target U V) (real G) ideal :=
  fun A ha => ⟨compSim relay A, child_witness G secure A ha⟩

/-- A named witness at the dummy, with no redundant forwarding layer in the simulator. -/
theorem dummy_witness (G : GeneratorFamily) (secure : G.Secure IsPPTBitStringTest) :
    Computational.Witness Child.party Child.network
      (Experiment.source Child.network) (Experiment.target _ _)
      (real G) ideal dummy relay := by
  refine ⟨⟨Child.relay_ppt, trivial⟩, fun _ _ hz => ⟨hz.1, trivial⟩, ?_⟩
  intro C Z hz aux haux
  simpa only [ideal, ← Experiment.translate_dummy uniformOutput aux C Z] using
    sample_close G secure (packed Experiment.dummy_eligible hz) aux haux
end Child

variable {I O N B U V : Type}
abbrev Adv (I O N B U V : Type) :=
  ExecAdversary 1 I O (N ⊕ Child.Q) (B ⊕ Child.R) U V
abbrev simulator (A : Adv I O N B U V) := compSim (hybridSim relay) A

variable (P : HybridProtocol 1 I O N B Word Result) (party : WordPort (Fin 1 × I) (Option O))
    (raw : WordPort N B) (ctl : WordPort U V)
abbrev net := Computational.outerNetPort party raw Child.party Child.raw

@[expose] def source : Computational.Profile 1 I O (N ⊕ Child.Q) (B ⊕ Child.R) U V where
  network := net party raw
  adversary _ := True
  tester A C Z := Computational.AdversaryCap party (net party raw) ctl A C Z ∧
    Computational.ParentCap P party raw Child.party Child.raw A C Z ∧
    Experiment.ServiceCut dummy C (Computational.innerTester P C A Z)

@[expose] def target : Computational.Profile 1 I O (N ⊕ Child.Q) (B ⊕ Child.R) U V where
  network := net party raw
  adversary _ := True
  tester _ _ _ := True

section Admission
variable {P party raw ctl} {A : Adv I O N B U V} {C : Finset (Fin 1)} {Z : Environment 1 I O U V}

theorem inner_admitted (hp : P.IsPPT party raw Child.party)
    (ha : (source P party raw ctl).Eligible ctl A)
    (hz : (source P party raw ctl).Tests party ctl A C Z) :
    (Experiment.source Child.network).Tests Child.party
      Child.network dummy C (Computational.innerTester P C A Z) := by
  have idx : ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1)
      encBits (encFinite (Fin 1)) :=
    (ComputableInPolyTime.const (encIn := encBits) (encOut := encFinite (Fin 1))
      (0 : Fin 1)).of_enc_eq (fun _ => congrArg _ (Subsingleton.elim _ _))
  exact ⟨Computational.innerTester_ppt_of_cuts hp idx ha.1 hz.1 hz.2.1 hz.2.2.1,
    Experiment.dummy_cap C _, hz.2.2.2⟩

theorem primitive_admissible (hp : P.IsPPT party raw Child.party)
    (ha : (source P party raw ctl).Eligible ctl A)
    (hz : (source P party raw ctl).Tests party ctl A C Z)
    {aux : Computational.Sampler} (hj : IsPPTOn encUnary encBits aux) :
    IsPPTBitStringTest (Primitive.sampleTest
      (Experiment.context C dummy (Computational.innerTester P C A Z)) aux) :=
  Primitive.sampleTest_admissible (packed Experiment.dummy_eligible (inner_admitted hp ha hz)) hj
end Admission

/-- Endpoint equality for a fixed draw isolates the effect of changing the command convention. -/
theorem translation_full (draw aux : Computational.Sampler) (A : Adv I O N B U V)
    (C : Finset (Fin 1)) (Z : Environment 1 I O U V) (κ : ℕ) :
    Computational.sampled (exec (compose P (protocol false draw)) A C Z) aux κ =
    Computational.sampled (exec (compose P (protocol true draw)) (simulator A) C Z) aux κ :=
  (Computational.real_endpoint P _ A C Z aux κ).trans
    ((Experiment.translate_dummy draw aux C _ κ).trans
      (Computational.ideal_endpoint P _ relay A C Z aux κ).symm)

/-- An efficient sampler for the generated word gives a strict-PPT sampler for the exact
decision bit of the admitted real execution. -/
theorem real_decision_ppt {P party raw ctl} {A : Adv I O N B U V}
    {C : Finset (Fin 1)} {Z : Environment 1 I O U V} {aux : Computational.Sampler}
    (G : GeneratorFamily) (hG : IsPPTOn encUnary encBits (generated G))
    (hp : P.IsPPT party raw Child.party) (ha : (source P party raw ctl).Eligible ctl A)
    (hz : (source P party raw ctl).Tests party ctl A C Z) (haux : IsPPTOn encUnary encBits aux) :
    ∃ sample : ℕ → ProbComp Bool, IsPPTOn encUnary encBool sample ∧
      ∀ κ, (sample κ).eval = Computational.sampled (exec (compose P (real G)) A C Z) aux κ := by
  let K := Experiment.context C dummy (Computational.innerTester P C A Z)
  have hK : Primitive.PackedPPT K := packed Experiment.dummy_eligible (inner_admitted hp ha hz)
  refine ⟨fun κ => generated G κ >>= Primitive.wordTest K aux κ,
    hG.bind_with (Primitive.wordTest_isPPT hK haux), ?_⟩
  intro κ
  rw [real, Computational.real_endpoint, Experiment.sampled_eq, ProbComp.eval_bind]

/-- Sampling a uniform challenge and running the primitive distinguisher gives a strict-PPT
sampler for the exact decision bit of the admitted ideal execution. -/
theorem ideal_decision_ppt {P party raw ctl} {A : Adv I O N B U V}
    {C : Finset (Fin 1)} {Z : Environment 1 I O U V} {aux : Computational.Sampler}
    (hp : P.IsPPT party raw Child.party) (ha : (source P party raw ctl).Eligible ctl A)
    (hz : (source P party raw ctl).Tests party ctl A C Z) (haux : IsPPTOn encUnary encBits aux) :
    ∃ sample : ℕ → ProbComp Bool, IsPPTOn encUnary encBool sample ∧
      ∀ κ, (sample κ).eval = Computational.sampled
        (exec (compose P ideal) (simulator A) C Z) aux κ := by
  let K := Experiment.context C dummy (Computational.innerTester P C A Z)
  have hK : Primitive.PackedPPT K := packed Experiment.dummy_eligible (inner_admitted hp ha hz)
  refine ⟨prgIdealGame (fun κ => 2 * κ) (Primitive.wordTest K aux),
    isPPTOn_prgIdealGame (by fun_prop) (Primitive.wordTest_isPPT hK haux), ?_⟩
  intro κ
  rw [prgIdealGame, ideal, ← translation_full P uniformOutput aux A C Z κ,
    Computational.real_endpoint, Experiment.sampled_eq, ProbComp.eval_bind, uniformOutput]

/-- Keep the outer simulator wrappers and substitute the forwarding child machine.
This gives precisely the reference execution with A alone, on actual typed routes. -/
theorem forwarding_full (inv : Bool) (draw aux : Computational.Sampler) (A : Adv I O N B U V)
    (C : Finset (Fin 1)) (Z : Environment 1 I O U V) (κ : ℕ) :
    Computational.sampled (exec (compose P (protocol inv draw))
      (compSim (hybridSim dummy) A) C Z) aux κ =
      Computational.sampled (exec (compose P (protocol inv draw)) A C Z) aux κ :=
  (Computational.ideal_endpoint P _ dummy A C Z aux κ).trans
    (Computational.real_endpoint P _ A C Z aux κ).symm

theorem prg_advantage_eq (G : GeneratorFamily) (A : Adv I O N B U V) (C : Finset (Fin 1))
    (Z : Environment 1 I O U V) (aux : Computational.Sampler) (κ : ℕ) :
    let D := Primitive.sampleTest
      (Experiment.context C dummy (Computational.innerTester P C A Z)) aux κ
    Game.advantage (Computational.sampled (exec (compose P (real G)) A C Z) aux κ)
      (Computational.sampled (exec (compose P ideal) (simulator A) C Z) aux κ) =
      Game.advantage ((G κ).realExperiment D) (PRG.Generator.idealExperiment D) := by
  rw [ideal, ← translation_full P uniformOutput aux A C Z κ,
    Computational.real_endpoint, Computational.real_endpoint P (protocol false uniformOutput)]
  exact Experiment.sampling_advantage G dummy C _ aux κ

theorem witness (hp : P.IsPPT party raw Child.party)
    (G : GeneratorFamily) (secure : G.Secure IsPPTBitStringTest)
    (A : Adv I O N B U V) (ha : (source P party raw ctl).Eligible ctl A) :
    Computational.Witness party ctl (source P party raw ctl) (target (U := U) (V := V) party raw)
      (compose P (real G)) (compose P ideal) A (simulator A) := by
  apply Computational.oneChildWitness P (real G) ideal relay party ctl Child.party
    Child.network _ _ _ _ (dummy_witness G secure) A ?_ ?_ ?_
  · exact ⟨Child.compSim_relay_ppt party raw ctl A ha.1, trivial⟩
  · exact fun _ _ hz => inner_admitted hp ha hz
  · exact fun _ _ hz _ => ⟨hz.1, trivial⟩

theorem emulates (hp : P.IsPPT party raw Child.party)
    (G : GeneratorFamily) (secure : G.Secure IsPPTBitStringTest) :
    Computational.EmulatesOn party ctl (source P party raw ctl) (target (U := U) (V := V) party raw)
      (compose P (real G)) (compose P ideal) :=
  fun A ha => ⟨simulator A, witness P party raw ctl hp G secure A ha⟩

end CslibFrontierTests.Crypto.UCComputational.Application
