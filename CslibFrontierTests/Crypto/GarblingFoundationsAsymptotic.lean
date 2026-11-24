/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

import CslibFrontier.Crypto.Primitives.Garbling.FoundationsAsymptotic
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Privacy
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Game.HiddenBit
import CslibFrontier.Crypto.Negligible.InversePolynomial
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for asymptotic garbling security notions and BHR12 Propositions 2 and 3

Positive sanity checks (`constFalseScheme`, valid and efficient, satisfying `PrvIndSecure`,
`PrvSimSecureUniversal`, `PrvSimSecure`, `ObvIndSecure`, `ObvSimSecureUniversal`, `ObvSimSecure`,
and `AutSecure`, plus `PointPermute.scheme` getting `PrvIndSecure` from `prvSim_pointPermute`) and
non-vacuous negative witnesses (`leakyPrvScheme` failing `PrvIndSecure`, `PrvSimSecure`,
`ObvIndSecure`, `ObvSimSecure`, and `ObvSimSecureUniversal`; `forgingScheme` failing `AutSecure`).
-/

namespace CslibFrontierTests.Crypto.GarblingFoundationsAsymptotic

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ## Positive instance: a constant-output scheme -/

/-- A valid, efficient scheme on `ℕ`-length bit strings whose semantics is constant `[false]`,
whose garbled view `(F, X, d)` is empty, and whose decoder accepts only the empty garbled output
`[]`. -/
def constFalseScheme : Scheme ℕ where
  inLen := id
  outLen _ := 1
  size := id
  ev _ _ := [false]
  coinLen _ _ _ _ := 0
  gb _ _ _ := ⟨[], [], []⟩
  encode _ _ := []
  evalGarbled _ _ := []
  decode _ Y := if Y == [] then some [false] else none

theorem constFalseScheme_isValid : constFalseScheme.IsValid where
  length _ _ _ _ _ _ hg _ hg' := by
    obtain ⟨_, -, rfl⟩ := constFalseScheme.mem_support_eval_garble_iff.mp hg
    obtain ⟨_, -, rfl⟩ := constFalseScheme.mem_support_eval_garble_iff.mp hg'
    exact ⟨rfl, rfl, rfl⟩
  nonDegenerate _ _ _ _ _ _ _ := ⟨rfl, rfl⟩
  correct _ _ _ _ _ g hg := by
    obtain ⟨_, -, rfl⟩ := constFalseScheme.mem_support_eval_garble_iff.mp hg
    rfl

theorem constFalseScheme_isEfficient : constFalseScheme.IsEfficient encUnary where
  inLen := ComputableInPolyTime.id'
  outLen := ComputableInPolyTime.const 1
  coins := ComputableInPolyTime.const 0
  gb := ComputableInPolyTime.const (⟨[], [], []⟩ : Scheme.Garbled)
  encode := ComputableInPolyTime.const []
  evalGarbled := ComputableInPolyTime.const []
  decode := by polytime [constFalseScheme]
  ev := ComputableInPolyTime.const [false]

theorem constFalseScheme_prvIndSecure :
    constFalseScheme.PrvIndSecure (SideInfo.circ constFalseScheme) encUnary := by
  intro σ encσ A _
  refine negligible_of_le negligible_zero fun k => ?_
  have hexp :
      ProbComp.eval (prvIndExperiment constFalseScheme (SideInfo.circ constFalseScheme) k (A k)
        false) =
      ProbComp.eval (prvIndExperiment constFalseScheme (SideInfo.circ constFalseScheme) k (A k)
        true) := by
    simp only [prvIndExperiment, ProbComp.eval_bind]
    congr 1
  rw [prvIndAdvantage, Experiment.advantage, hexp, Game.advantage_self]

/-- An efficient `(Φ_circ, ev)`-inverter for `constFalseScheme`: return `(n, 0^n)`. -/
def constFalseEvInverter : ℕ → List Bool → Query ℕ :=
  fun n _ => ⟨n, List.replicate n false⟩

theorem constFalseEvInverter_isEvInverter :
    (SideInfo.circ constFalseScheme).IsEvInverter constFalseScheme constFalseEvInverter :=
  fun _ _ _ => ⟨rfl, List.length_replicate, rfl⟩

theorem constFalseEvInverter_polyTime :
    ComputableInPolyTime (fun p : ℕ × List Bool => constFalseEvInverter p.1 p.2)
      (encPair encUnary encBits) (encQuery ℕ encUnary) := by
  unfold constFalseEvInverter
  polytime

theorem constFalseScheme_prvSimSecureUniversal :
    constFalseScheme.PrvSimSecureUniversal (SideInfo.circ constFalseScheme) encUnary encUnary :=
  constFalseScheme_prvIndSecure.prvSimSecureUniversal (SideInfo.circ_compatible _)
    constFalseScheme_isEfficient .id' constFalseEvInverter_isEvInverter
    constFalseEvInverter_polyTime

theorem constFalseScheme_prvSimSecure :
    constFalseScheme.PrvSimSecure (SideInfo.circ constFalseScheme) encUnary encUnary :=
  constFalseScheme_prvIndSecure.prvSimSecure (SideInfo.circ_compatible _)
    constFalseScheme_isEfficient .id' constFalseEvInverter_isEvInverter
    constFalseEvInverter_polyTime

theorem constFalseScheme_obvIndSecure :
    constFalseScheme.ObvIndSecure (SideInfo.circ constFalseScheme) encUnary := by
  intro σ encσ A _
  refine negligible_of_le negligible_zero fun k => ?_
  have hexp :
      ProbComp.eval (obvIndExperiment constFalseScheme (SideInfo.circ constFalseScheme) k (A k)
        false) =
      ProbComp.eval (obvIndExperiment constFalseScheme (SideInfo.circ constFalseScheme) k (A k)
        true) := by
    simp only [obvIndExperiment, ProbComp.eval_bind]
    congr 1
  rw [obvIndAdvantage, Experiment.advantage, hexp, Game.advantage_self]

theorem constFalseScheme_obvSimSecureUniversal :
    constFalseScheme.ObvSimSecureUniversal (SideInfo.circ constFalseScheme) encUnary encUnary :=
  constFalseScheme_obvIndSecure.obvSimSecureUniversal (SideInfo.circ_compatible _)
    constFalseScheme_isEfficient .id' (SideInfo.circ_isInverter _) .id'

theorem constFalseScheme_obvSimSecure :
    constFalseScheme.ObvSimSecure (SideInfo.circ constFalseScheme) encUnary encUnary :=
  constFalseScheme_obvIndSecure.obvSimSecure (SideInfo.circ_compatible _)
    constFalseScheme_isEfficient .id' (SideInfo.circ_isInverter _) .id'

theorem constFalseScheme_autSecure : constFalseScheme.AutSecure encUnary := by
  intro σ encσ A _
  refine negligible_of_le negligible_zero fun k => ?_
  have hexp : ProbComp.eval (autExperiment constFalseScheme k (A k)) = PMF.pure false := by
    simp only [autExperiment, ProbComp.eval_bind]
    refine .trans ?_ (PMF.bind_const (ProbComp.eval ((A k).choose ())) (PMF.pure false))
    congr 1
    funext ⟨q, st⟩
    by_cases hlen : q.input.length = constFalseScheme.inLen q.fn
    · simp only [hlen, ↓reduceIte, Scheme.garble, Scheme.coins, ProbComp.eval_bind,
        BitString.eval_sampleList, BitString.uniformList_zero, ProbComp.eval_pure, constFalseScheme,
        PMF.pure_bind, PMF.bind_const]
      refine .trans ?_
        (PMF.bind_const (ProbComp.eval ((A k).guess st ⟨[], []⟩)) (PMF.pure false))
      congr 1
      funext forged
      cases forged with
      | nil => simp
      | cons b bs => simp
    · simp [hlen]
  rw [← NNReal.coe_le_coe, NNReal.coe_zero, autAdvantage, Experiment.coe_succProbability, hexp]
  simp

/-! ## Representative caller: `PointPermute` gains `PrvIndSecure` from `prvSim_pointPermute` -/

theorem pointPermute_prvIndSecure {family : List Bool → List Bool → List Bool}
    (h : PseudorandomFunction family) :
    (PointPermute.scheme family).PrvIndSecure phiTopo encValidCircuit :=
  (h.prvSim_pointPermute).prvIndSecure
    (phiTopo_compatible (PointPermute.scheme_isCircuitScheme family))
    (PointPermute.scheme_isEfficient h.polyTime)
    phiTopo_polyTime

/-! ## Negative counterexamples (non-vacuity) -/

/-- A scheme of functions with no output whose garbled input is the input itself. -/
def leakyPrvScheme : Scheme ℕ where
  inLen := id
  outLen _ := 0
  size := id
  ev _ _ := []
  coinLen _ _ _ _ := 0
  gb _ _ _ := ⟨[], [], []⟩
  encode _ x := x
  evalGarbled _ _ := []
  decode _ _ := some []

theorem leakyPrvScheme_isEfficient : leakyPrvScheme.IsEfficient encUnary where
  inLen := ComputableInPolyTime.id'
  outLen := ComputableInPolyTime.const 0
  coins := ComputableInPolyTime.const 0
  gb := ComputableInPolyTime.const (⟨[], [], []⟩ : Scheme.Garbled)
  encode := ComputableInPolyTime.snd encBits encBits
  evalGarbled := ComputableInPolyTime.const []
  decode := ComputableInPolyTime.const (some ([] : List Bool))
  ev := ComputableInPolyTime.const []

/-- An adversary breaking `PrvIndSecure` of `leakyPrvScheme`: submit `([false], [true])` on
function `1` and read the first bit of the garbled input `X`. -/
def leakyPrvIndAdversary : ℕ → PrvIndAdversary ℕ Unit := fun _ =>
  { choose := fun _ => pure (⟨⟨1, [false]⟩, ⟨1, [true]⟩⟩, ())
    guess := fun _ V => pure ((V.getD ⟨[], [], []⟩).input.getD 0 false) }

theorem isPPT_leakyPrvIndAdversary :
    TwoStage.IsPPT encUnit (encMessagePair (encQuery ℕ encUnary)) (encOption encPrvView) encBool
      encUnit leakyPrvIndAdversary where
  choose := (ComputableInPolyTime.const
    ((⟨⟨1, [false]⟩, ⟨1, [true]⟩⟩ : MessagePair (Query ℕ)), ())).isPPTOn.congr
      fun ⟨_, _⟩ => rfl
  guess := by
    let E := encPair encUnary (encPair encUnit (encOption encPrvView))
    have hV : ComputableInPolyTime
        (fun p : ℕ × Unit × Option PrvView => p.2.2.getD ⟨[], [], []⟩) E encPrvView :=
      ComputableInPolyTime.optionGetDWithInput
        (ComputableInPolyTime.snd encUnary (encPair encUnit (encOption encPrvView))).snd'
        (ComputableInPolyTime.const (⟨[], [], []⟩ : PrvView))
    have hbit : ComputableInPolyTime
        (fun p : ℕ × Unit × Option PrvView => (p.2.2.getD ⟨[], [], []⟩).input.getD 0 false)
        E encBool :=
      (encPrvView_input_polyTime hV).bitsGetDWithInput (ComputableInPolyTime.const 0) false
    exact hbit.isPPTOn.congr fun ⟨_, _, _⟩ => rfl

theorem not_prvIndSecure_leakyPrvScheme :
    ¬ leakyPrvScheme.PrvIndSecure (SideInfo.circ leakyPrvScheme) encUnary := by
  intro hsec
  have hneg := hsec _ encUnit leakyPrvIndAdversary isPPT_leakyPrvIndAdversary
  have hadv : ∀ k, prvIndAdvantage leakyPrvScheme (SideInfo.circ leakyPrvScheme) k
      (leakyPrvIndAdversary k) = 1 := by
    intro k
    have h0 : ProbComp.eval (prvIndExperiment leakyPrvScheme (SideInfo.circ leakyPrvScheme) k
        (leakyPrvIndAdversary k) false) = PMF.pure false := by
      simp [prvIndExperiment, leakyPrvIndAdversary, prvIndValid, leakyPrvScheme,
        Scheme.prvView, Scheme.garble, Scheme.coins, BitString.uniformList_zero, SideInfo.circ]
    have h1 : ProbComp.eval (prvIndExperiment leakyPrvScheme (SideInfo.circ leakyPrvScheme) k
        (leakyPrvIndAdversary k) true) = PMF.pure true := by
      simp [prvIndExperiment, leakyPrvIndAdversary, prvIndValid, leakyPrvScheme,
        Scheme.prvView, Scheme.garble, Scheme.coins, BitString.uniformList_zero, SideInfo.circ]
    rw [← NNReal.coe_eq_one, prvIndAdvantage, Experiment.coe_advantage, h0, h1]
    simp
  exact not_negligible_const (c := 1) one_ne_zero (hneg.congr' (Filter.Eventually.of_forall hadv))

theorem not_prvSimSecure_leakyPrvScheme :
    ¬ leakyPrvScheme.PrvSimSecure (SideInfo.circ leakyPrvScheme) encUnary encUnary :=
  fun h => not_prvIndSecure_leakyPrvScheme
    (h.prvIndSecure (SideInfo.circ_compatible _) leakyPrvScheme_isEfficient .id')

/-- An adversary breaking `ObvIndSecure` of `leakyPrvScheme`: submit `([false], [true])` on
function `1` and read the first bit of the garbled input `X`. -/
def leakyObvIndAdversary : ℕ → ObvIndAdversary ℕ Unit := fun _ =>
  { choose := fun _ => pure (⟨⟨1, [false]⟩, ⟨1, [true]⟩⟩, ())
    guess := fun _ V => pure ((V.getD ⟨[], []⟩).input.getD 0 false) }

theorem isPPT_leakyObvIndAdversary :
    TwoStage.IsPPT encUnit (encMessagePair (encQuery ℕ encUnary)) (encOption encObvView) encBool
      encUnit leakyObvIndAdversary where
  choose := (ComputableInPolyTime.const
    ((⟨⟨1, [false]⟩, ⟨1, [true]⟩⟩ : MessagePair (Query ℕ)), ())).isPPTOn.congr
      fun ⟨_, _⟩ => rfl
  guess := by
    let E := encPair encUnary (encPair encUnit (encOption encObvView))
    have hV : ComputableInPolyTime
        (fun p : ℕ × Unit × Option ObvView => p.2.2.getD ⟨[], []⟩) E encObvView :=
      ComputableInPolyTime.optionGetDWithInput
        (ComputableInPolyTime.snd encUnary (encPair encUnit (encOption encObvView))).snd'
        (ComputableInPolyTime.const (⟨[], []⟩ : ObvView))
    have hbit : ComputableInPolyTime
        (fun p : ℕ × Unit × Option ObvView => (p.2.2.getD ⟨[], []⟩).input.getD 0 false)
        E encBool :=
      (encObvView_input_polyTime hV).bitsGetDWithInput (ComputableInPolyTime.const 0) false
    exact hbit.isPPTOn.congr fun ⟨_, _, _⟩ => rfl

theorem not_obvIndSecure_leakyPrvScheme :
    ¬ leakyPrvScheme.ObvIndSecure (SideInfo.circ leakyPrvScheme) encUnary := by
  intro hsec
  have hneg := hsec _ encUnit leakyObvIndAdversary isPPT_leakyObvIndAdversary
  have hadv : ∀ k, obvIndAdvantage leakyPrvScheme (SideInfo.circ leakyPrvScheme) k
      (leakyObvIndAdversary k) = 1 := by
    intro k
    have h0 : ProbComp.eval (obvIndExperiment leakyPrvScheme (SideInfo.circ leakyPrvScheme) k
        (leakyObvIndAdversary k) false) = PMF.pure false := by
      simp [obvIndExperiment, leakyObvIndAdversary, obvIndValid, leakyPrvScheme,
        Scheme.obvView, Scheme.garble, Scheme.coins, BitString.uniformList_zero, SideInfo.circ]
    have h1 : ProbComp.eval (obvIndExperiment leakyPrvScheme (SideInfo.circ leakyPrvScheme) k
        (leakyObvIndAdversary k) true) = PMF.pure true := by
      simp [obvIndExperiment, leakyObvIndAdversary, obvIndValid, leakyPrvScheme,
        Scheme.obvView, Scheme.garble, Scheme.coins, BitString.uniformList_zero, SideInfo.circ]
    rw [← NNReal.coe_eq_one, obvIndAdvantage, Experiment.coe_advantage, h0, h1]
    simp
  exact not_negligible_const (c := 1) one_ne_zero (hneg.congr' (Filter.Eventually.of_forall hadv))

theorem not_obvSimSecure_leakyPrvScheme :
    ¬ leakyPrvScheme.ObvSimSecure (SideInfo.circ leakyPrvScheme) encUnary encUnary :=
  fun h => not_obvIndSecure_leakyPrvScheme
    (h.obvIndSecure (SideInfo.circ_compatible _) leakyPrvScheme_isEfficient .id')

theorem not_obvSimSecureUniversal_leakyPrvScheme :
    ¬ leakyPrvScheme.ObvSimSecureUniversal (SideInfo.circ leakyPrvScheme) encUnary encUnary :=
  fun h => not_obvSimSecure_leakyPrvScheme h.obvSimSecure

/-- A scheme whose decoder accepts any output of the right length, failing authenticity. -/
def forgingScheme : Scheme ℕ where
  inLen := id
  outLen := id
  size := id
  ev _ x := x
  coinLen _ _ _ _ := 0
  gb _ n _ := ⟨[], [], List.replicate n false⟩
  encode _ x := x
  evalGarbled _ x := x
  decode d y := if y.length = d.length then some y else none

/-- An adversary breaking `AutSecure` of `forgingScheme`: query `1` on `[false]` and forge
`[true]`. -/
def forgingAdversary : ℕ → AutAdversary ℕ Unit := fun _ =>
  { choose := fun _ => pure (⟨1, [false]⟩, ())
    guess := fun _ _ => pure [true] }

theorem isPPT_forgingAdversary :
    TwoStage.IsPPT encUnit (encQuery ℕ encUnary) encObvView encBits encUnit forgingAdversary where
  choose := (ComputableInPolyTime.const ((⟨1, [false]⟩ : Query ℕ), ())).isPPTOn.congr
    fun ⟨_, _⟩ => rfl
  guess := (ComputableInPolyTime.const ([true] : List Bool)).isPPTOn.congr fun ⟨_, _, _⟩ => rfl

theorem not_autSecure_forgingScheme : ¬ forgingScheme.AutSecure encUnary := by
  intro hsec
  have hneg := hsec _ encUnit forgingAdversary isPPT_forgingAdversary
  have hadv : ∀ k, autAdvantage forgingScheme k (forgingAdversary k) = 1 := by
    intro k
    have hexp : ProbComp.eval (autExperiment forgingScheme k (forgingAdversary k)) =
        PMF.pure true := by
      simp [autExperiment, forgingAdversary, forgingScheme, Scheme.garble, Scheme.coins,
        BitString.uniformList_zero]
      rfl
    rw [← NNReal.coe_eq_one, autAdvantage, Experiment.coe_succProbability, hexp]
    simp
  exact not_negligible_const (c := 1) one_ne_zero (hneg.congr' (Filter.Eventually.of_forall hadv))

end CslibFrontierTests.Crypto.GarblingFoundationsAsymptotic
