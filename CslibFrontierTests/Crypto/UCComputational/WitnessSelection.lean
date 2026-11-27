/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: local-only (test)

public import CslibFrontierTests.Crypto.UCComputational.Routes
import CslibFrontier.Crypto.Negligible.Basic

/-!
# Selecting the translator from child emulation

The real child profile admits the dummy adversary. The ideal child profile admits both the
translator and a plain forwarder. On the admitted tag tester the forwarder has advantage one
at every security parameter. Any child security witness must therefore use the translator,
whose composition with an arbitrary eligible outer adversary has a strict-PPT certificate.
-/

namespace CslibFrontierTests.Crypto.UCComputational.WitnessSelection

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

private abbrev realChild :=
  { Experiment.source Child.network with adversary := fun A => A = Experiment.dummy }

private abbrev idealChild :=
  { Experiment.target Child.Q Child.R with
    adversary := fun S => S = Child.relay ∨ S = Experiment.dummy }

private theorem restricted_child (G : Primitive.GeneratorFamily)
    (sec : G.Secure IsPPTBitStringTest) :
    Computational.EmulatesOn Child.party Child.network realChild idealChild
      (Application.real G) Application.ideal := by
  intro A ha
  have hA : A = Experiment.dummy := ha.2
  subst A
  let w := Application.dummy_witness G sec
  exact ⟨Child.relay, ⟨⟨w.eligible.1, Or.inl rfl⟩, w.carry, w.close⟩⟩

/-- The forwarding machine qualifies at the ideal port, but its unit gap on the admitted
tag tester prevents it from witnessing child security. -/
private theorem only_translator (G : Primitive.GeneratorFamily) {S}
    (w : Computational.Witness Child.party Child.network realChild idealChild
      (Application.real G) Application.ideal Experiment.dummy S) : S = Child.relay := by
  rcases w.eligible.2 with correct | forward
  · exact correct
  · subst S
    let aux : Computational.Sampler := fun _ => pure []
    have haux : IsPPTOn encUnary encBits aux :=
      (ComputableInPolyTime.const (encIn := encUnary) (encOut := encBits) []).isPPTOn
    have ht := Application.inner_admitted (Test.parent_ppt false)
      (A := Test.A) (ctl := Test.net)
      ⟨Adversary.isPPT_dummyAdversary 1 Test.net, trivial⟩ (Test.admitted false ∅)
    have negligible := w.close ∅ _ ht aux haux
    exfalso
    apply not_negligible_const one_ne_zero (negligible.congr' (Filter.Eventually.of_forall ?_))
    intro k
    simpa only [Computational.real_endpoint (Test.parent false) (Application.real G) Test.A,
      Computational.ideal_endpoint (Test.parent false) Application.ideal Experiment.dummy Test.A]
      using Test.forward_only_gap (Primitive.generated G) Primitive.uniformOutput aux ∅ k

/-- Lift child emulation by identifying which eligible candidate witnesses security. -/
public theorem emulates {I O N B U V : Type} (P : HybridProtocol 1 I O N B Child.Word Child.Result)
    (party : WordPort (Fin 1 × I) (Option O)) (raw : WordPort N B) (ctl : WordPort U V)
    (hp : P.IsPPT party raw Child.party) (G : Primitive.GeneratorFamily)
    (sec : G.Secure IsPPTBitStringTest) :
    Computational.EmulatesOn party ctl (Application.source P party raw ctl)
      (Application.target party raw) (compose P (Application.real G))
      (compose P Application.ideal) := by
  apply Computational.oneChild_of_emulates P (Application.real G) Application.ideal party ctl
    Child.party Child.network _ _ realChild idealChild (restricted_child G sec)
    ⟨Experiment.dummy_eligible.1, rfl⟩
  · intro S hw A ha
    have same : S = Child.relay := only_translator G hw
    subst S
    exact ⟨Child.compSim_relay_ppt party raw ctl A ha.1, trivial⟩
  · exact fun _ ha _ _ hz => Application.inner_admitted hp ha hz
  · exact fun _ _ _ _ _ _ hz _ => ⟨hz.1, trivial⟩

end CslibFrontierTests.Crypto.UCComputational.WitnessSelection
