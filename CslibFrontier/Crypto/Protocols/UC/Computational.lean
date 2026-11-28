/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.UC.Composition
public import CslibFrontier.Crypto.Protocols.UC.PPT.Execution

/-!
# Computational replacement of one fixed UC child

A tester supplies party inputs, controls an adversary and observes one bit. A sampler draws its
auxiliary input on the unary security parameter. The sampler and tester are uniform strict-PPT
programs. A resource profile specifies the network encoding and any further admission conditions
for adversaries and testers. The ideal profile receives the same tester under the same static
corruption set, which lets a second replacement use the simulator chosen by the first.

## Main definitions

* `Cslib.Crypto.Protocols.UC.Computational.EmulatesOn` chooses one eligible simulator for each
  eligible adversary before the corruption set, tester and auxiliary-input distribution are chosen.
* `Cslib.Crypto.Protocols.UC.Computational.Witness` records that simulator's eligibility,
  transport of admitted testers, and negligible distinguishing advantage.

## Main results

* `Cslib.Crypto.Protocols.UC.Computational.EmulatesOn.trans` composes replacements with a common
  intermediate profile.
* `Cslib.Crypto.Protocols.UC.Computational.oneChildWitness` lifts a witness for the child under the
  dummy adversary. Its premises certify the full simulator and the admission of testers across the
  two interfaces. `Cslib.Crypto.Protocols.UC.Computational.oneChild_of_emulates` selects the witness
  from child emulation when these premises hold for every simulator witnessing the dummy case.
* `Cslib.Crypto.Protocols.UC.Computational.innerTester_ppt_of_cuts` proves strict PPT of the
  child tester from reachable reply bounds at the adversary and parent.

These are original rules for Frontier's typed, fixed-party, static-corruption execution (#6043).
The PPT conditions here govern the adversary, simulator, tester, and auxiliary-input sampler.
Running-time certificates for protocol code are separate. The endpoint identities use the existing
single-child routing equations.
-/

public section

namespace Cslib.Crypto.Protocols.UC.Computational

open Cslib.Probability Turing.MultiTapeTM

/-- Auxiliary-input sampler indexed by the security parameter. -/
abbrev Sampler := ℕ → ProbComp (List Bool)

/-- A Boolean execution given the security parameter and auxiliary input. -/
abbrev Run := ℕ → List Bool → ProbComp Bool

/-- Sample the auxiliary word once, then run the typed execution at that input. -/
@[expose] noncomputable def sampled (run : Run) (draw : Sampler) (k : ℕ) : Game :=
  (draw k).eval.bind fun z => (run k z).eval

/-- Negligible distinguishing advantage for each uniform strict-PPT auxiliary-input sampler. -/
abbrev Close (x y : Run) : Prop :=
  Game.Indistinguishable (sampled x) (sampled y) (IsPPTOn encUnary encBits)

/-- Identical output laws at every auxiliary word suffice for sampled indistinguishability. -/
theorem Close.of_eval_eq {x y : Run} (h : ∀ k z, (x k z).eval = (y k z).eval) :
    Close x y := by
  intro draw _
  simp [sampled, h]

/-- The encoding of the routed network port and the resource conditions on its participants. -/
structure Profile (n : ℕ) (I O NQ NR Q R : Type) where
  /-- Encoding used to certify adversaries at this endpoint. -/
  network : WordPort (RoutedNetQ n I NQ) (RoutedNetR O NR)
  /-- Additional admission condition on the entire adversary family. -/
  adversary : ExecAdversary n I O NQ NR Q R → Prop
  /-- Additional admission condition on a tester for this adversary and corruption set. -/
  tester : ExecAdversary n I O NQ NR Q R → Finset (Fin n) → Environment n I O Q R → Prop

namespace Profile
variable {n : ℕ} {I O NQ NR Q R : Type}

/-- The adversary has a strict-PPT certificate and meets the endpoint admission condition. -/
@[expose] def Eligible (p : Profile n I O NQ NR Q R) (control : WordPort Q R)
    (A : ExecAdversary n I O NQ NR Q R) : Prop :=
  A.IsPPT p.network control ∧ p.adversary A

/-- The environment has a strict-PPT certificate and meets the condition for this interaction. -/
@[expose] def Tests (p : Profile n I O NQ NR Q R) (party : WordPort (Fin n × I) (Option O))
    (control : WordPort Q R) (A : ExecAdversary n I O NQ NR Q R)
    (C : Finset (Fin n)) (Z : Environment n I O Q R) : Prop :=
  Z.IsPPT party control ∧ p.tester A C Z
end Profile

section Security
variable {n : ℕ} {I O N₁ R₁ N₂ R₂ N₃ R₃ Q R : Type}

/-- Security of a designated simulator. Both executions use the same environment-facing word
ports, corruption set, environment and auxiliary-input sampler. -/
structure Witness (party : WordPort (Fin n × I) (Option O)) (control : WordPort Q R)
    (p : Profile n I O N₁ R₁ Q R) (t : Profile n I O N₂ R₂ Q R)
    (X : Protocol n I O N₁ R₁) (F : Protocol n I O N₂ R₂)
    (A : ExecAdversary n I O N₁ R₁ Q R) (S : ExecAdversary n I O N₂ R₂ Q R) : Prop where
  /-- The simulator qualifies as an adversary for the ideal endpoint. -/
  eligible : t.Eligible control S
  /-- Every admitted real test remains admitted with the simulator. -/
  carry : ∀ C Z, p.Tests party control A C Z → t.Tests party control S C Z
  /-- Every admitted real test has negligible distinguishing advantage. -/
  close : ∀ C Z, p.Tests party control A C Z → Close (exec X A C Z) (exec F S C Z)

/-- For each eligible adversary, one simulator works for every admitted test and sampler. -/
@[expose] def EmulatesOn (party : WordPort (Fin n × I) (Option O)) (control : WordPort Q R)
    (p : Profile n I O N₁ R₁ Q R) (t : Profile n I O N₂ R₂ Q R)
    (X : Protocol n I O N₁ R₁) (F : Protocol n I O N₂ R₂) : Prop :=
  ∀ A, p.Eligible control A → ∃ S, Witness party control p t X F A S

section Transitivity
variable {party : WordPort (Fin n × I) (Option O)} {control : WordPort Q R}
    {p : Profile n I O N₁ R₁ Q R} {t : Profile n I O N₂ R₂ Q R}
    {u : Profile n I O N₃ R₃ Q R}
    {X : Protocol n I O N₁ R₁} {F : Protocol n I O N₂ R₂} {G : Protocol n I O N₃ R₃}

/-- Chain two designated simulations through the same middle adversary and profile. -/
theorem Witness.trans {A : ExecAdversary n I O N₁ R₁ Q R}
    {S : ExecAdversary n I O N₂ R₂ Q R} {T : ExecAdversary n I O N₃ R₃ Q R}
    (first : Witness party control p t X F A S) (second : Witness party control t u F G S T) :
    Witness party control p u X G A T :=
  ⟨second.eligible, fun C Z hz => second.carry C Z (first.carry C Z hz),
    fun C Z hz => Game.Indistinguishable.trans (first.close C Z hz)
      (second.close C Z (first.carry C Z hz))⟩

/-- Reuse the first simulator as an eligible adversary at the middle endpoint. -/
theorem EmulatesOn.trans
    (first : EmulatesOn party control p t X F) (second : EmulatesOn party control t u F G) :
    EmulatesOn party control p u X G := by
  intro A ha
  obtain ⟨S, lower⟩ := first A ha
  obtain ⟨T, upper⟩ := second S lower.eligible
  exact ⟨T, lower.trans upper⟩
end Transitivity
end Security

section OneChild
variable {n : ℕ} {I O N B J K XQ XR FQ FR Q R : Type}
  (P : HybridProtocol n I O N B J K) (X : Protocol n J K XQ XR) (F : Protocol n J K FQ FR)

variable (D : ExecAdversary n J K FQ FR (RoutedNetQ n J XQ) (RoutedNetR K XR))

/-- The child-only tester runs the outer tester, adversary and statically routed parent. -/
abbrev innerTester (C : Finset (Fin n))
    (A : ExecAdversary n I O (N ⊕ RoutedNetQ n J XQ) (B ⊕ RoutedNetR K XR) Q R)
    (Z : Environment n I O Q R) := absorbHybrid C P (absorbAdversary C A Z)

/-- The full routed real network interface. Successive sum tags choose the parent
party, parent raw network, child party, or child raw network. -/
abbrev outerNetPort (party : WordPort (Fin n × I) (Option O)) (raw : WordPort N B)
    (sub : WordPort (Fin n × J) (Option K)) (subNet : WordPort XQ XR) :=
  WordPort.sum party (WordPort.sum raw (WordPort.sum sub subNet))

/-- Reachable replies when the tester runs the outer adversary internally. -/
abbrev AdversaryCap {U V : Type}
    (party : WordPort (Fin n × I) (Option O)) (net : WordPort U V) (control : WordPort Q R)
    (A : Adversary n Q R U V) (C : Finset (Fin n)) (Z : Environment n I O Q R) :=
  ReplyCap (fun k set => liftAdversary (A k set)) (WordInterface.exec party net) party control C Z

/-- Reachable parent replies after the tester has absorbed the adversary. -/
abbrev ParentCap (party : WordPort (Fin n × I) (Option O)) (raw : WordPort N B)
    (sub : WordPort (Fin n × J) (Option K)) (subNet : WordPort XQ XR)
    (A : ExecAdversary n I O (N ⊕ RoutedNetQ n J XQ) (B ⊕ RoutedNetR K XR) Q R)
    (C : Finset (Fin n)) (Z : Environment n I O Q R) :=
  ReplyCap (fun k set => routeCorrupt set (hybridWrap (P k set)))
    (WordInterface.exec sub (WordPort.sum sub subNet)) party (outerNetPort party raw sub subNet)
    C (absorbAdversary C A Z)

section Resource
variable {P} {party : WordPort (Fin n × I) (Option O)} {raw : WordPort N B}
    {sub : WordPort (Fin n × J) (Option K)} {subNet : WordPort XQ XR} {control : WordPort Q R}
    {A : ExecAdversary n I O (N ⊕ RoutedNetQ n J XQ) (B ⊕ RoutedNetR K XR) Q R}
    {C : Finset (Fin n)} {Z : Environment n I O Q R}

/-- Absorbing the adversary and parent preserves strict PPT when both links have reachable caps. -/
theorem innerTester_ppt_of_cuts (hP : P.IsPPT party raw sub)
    (hidx : ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1)
      encBits (encFinite (Fin n)))
    (hA : A.IsPPT (outerNetPort party raw sub subNet) control) (hZ : Z.IsPPT party control)
    (capA : AdversaryCap party (outerNetPort party raw sub subNet) control A C Z)
    (capP : ParentCap P party raw sub subNet A C Z) :
    (innerTester P C A Z).IsPPT sub (WordPort.sum sub subNet) := by
  obtain ⟨L, hc, fit⟩ := capA
  have hAZ := hZ.link_of_reachable (hA.liftAdversary (party := party)) C L hc fit
  obtain ⟨L, hc, fit⟩ := capP
  exact hAZ.absorbHybrid_of_reachable hidx hP C L hc fit
end Resource

/-- Moving the adversary and parent into the tester preserves the real sampled output law. -/
theorem real_endpoint
    (A : ExecAdversary n I O (N ⊕ RoutedNetQ n J XQ) (B ⊕ RoutedNetR K XR) Q R)
    (C : Finset (Fin n)) (Z : Environment n I O Q R) (draw : Sampler) (κ : ℕ) :
    sampled (exec (compose P X) A C Z) draw κ =
    sampled (exec X (dummyAdversary n _ _) C (innerTester P C A Z)) draw κ := by
  unfold sampled
  congr 1
  funext z
  rw [exec_eq_exec_dummy (compose P X) A, exec_compose_dummy]

/-- Moving the parent and outer adversary into the tester leaves the child simulator in its
network position and preserves the ideal sampled output law. -/
theorem ideal_endpoint
    (A : ExecAdversary n I O (N ⊕ RoutedNetQ n J XQ) (B ⊕ RoutedNetR K XR) Q R)
    (C : Finset (Fin n)) (Z : Environment n I O Q R) (draw : Sampler) (κ : ℕ) :
    sampled (exec (compose P F) (compSim (hybridSim D) A) C Z) draw κ =
    sampled (exec F D C (innerTester P C A Z)) draw κ := by
  unfold sampled
  congr 1
  funext z
  rw [exec_compSim, eval_exec_compose_hybridSim]

section Designated
variable
    (party : WordPort (Fin n × I) (Option O)) (control : WordPort Q R)
    (childParty : WordPort (Fin n × J) (Option K))
    (childControl : WordPort (RoutedNetQ n J XQ) (RoutedNetR K XR))
    (p : Profile n I O (N ⊕ RoutedNetQ n J XQ) (B ⊕ RoutedNetR K XR) Q R)
    (t : Profile n I O (N ⊕ RoutedNetQ n J FQ) (B ⊕ RoutedNetR K FR) Q R)
    (px : Profile n J K XQ XR (RoutedNetQ n J XQ) (RoutedNetR K XR))
    (pf : Profile n J K FQ FR (RoutedNetQ n J XQ) (RoutedNetR K XR))
    (child : Witness childParty childControl px pf X F (dummyAdversary n _ _) D)
    (A : ExecAdversary n I O (N ⊕ RoutedNetQ n J XQ) (B ⊕ RoutedNetR K XR) Q R)

include child

/-- Lift a designated child witness through this parent and outer adversary. The three resource
premises certify the composed simulator, admit the absorbed tester for the real child, and return
its ideal admission to the outer interface. -/
theorem oneChildWitness
    (sim : t.Eligible control (compSim (hybridSim D) A))
    (absorb : ∀ C Z, p.Tests party control A C Z →
      px.Tests childParty childControl (dummyAdversary n _ _) C (innerTester P C A Z))
    (carry : ∀ C Z, p.Tests party control A C Z →
      pf.Tests childParty childControl D C (innerTester P C A Z) →
      t.Tests party control (compSim (hybridSim D) A) C Z) :
    Witness party control p t (compose P X) (compose P F) A (compSim (hybridSim D) A) := by
  refine ⟨sim, ?_, ?_⟩
  · intro C Z hz
    exact carry C Z hz (child.carry C _ (absorb C Z hz))
  · intro C Z hz draw hdraw
    have h := child.close C _ (absorb C Z hz) draw hdraw
    simpa only [ideal_endpoint P F D A, real_endpoint P X A] using h

end Designated

/-- Child emulation supplies a witness for the dummy adversary. The resource premises may
use all properties of that witness to lift it through an eligible outer adversary. For a
specific simulator with its own cost proof, use `oneChildWitness` directly. -/
theorem oneChild_of_emulates
    (party : WordPort (Fin n × I) (Option O)) (control : WordPort Q R)
    (childParty : WordPort (Fin n × J) (Option K))
    (childControl : WordPort (RoutedNetQ n J XQ) (RoutedNetR K XR))
    (p : Profile n I O (N ⊕ RoutedNetQ n J XQ) (B ⊕ RoutedNetR K XR) Q R)
    (t : Profile n I O (N ⊕ RoutedNetQ n J FQ) (B ⊕ RoutedNetR K FR) Q R)
    (px : Profile n J K XQ XR (RoutedNetQ n J XQ) (RoutedNetR K XR))
    (pf : Profile n J K FQ FR (RoutedNetQ n J XQ) (RoutedNetR K XR))
    (child : EmulatesOn childParty childControl px pf X F)
    (hdummy : px.Eligible childControl (dummyAdversary n _ _))
    (sim : ∀ S, Witness childParty childControl px pf X F (dummyAdversary n _ _) S →
      ∀ A, p.Eligible control A →
      t.Eligible control (compSim (hybridSim S) A))
    (absorb : ∀ A, p.Eligible control A → ∀ C Z, p.Tests party control A C Z →
      px.Tests childParty childControl (dummyAdversary n _ _) C (innerTester P C A Z))
    (carry : ∀ S, Witness childParty childControl px pf X F (dummyAdversary n _ _) S →
      ∀ A, p.Eligible control A →
      ∀ C Z, p.Tests party control A C Z →
        pf.Tests childParty childControl S C (innerTester P C A Z) →
      t.Tests party control (compSim (hybridSim S) A) C Z) :
    EmulatesOn party control p t (compose P X) (compose P F) := by
  obtain ⟨S, witness⟩ := child _ hdummy
  intro A ha
  exact ⟨compSim (hybridSim S) A,
    oneChildWitness P X F S party control childParty childControl p t px pf witness A
      (sim S witness A ha) (absorb A ha) (carry S witness A ha)⟩
end OneChild
end Cslib.Crypto.Protocols.UC.Computational
