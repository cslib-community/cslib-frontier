/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Primitives.Garbling.Basic
import CslibFrontier.Crypto.Primitives.Garbling.Foundations
import CslibFrontier.Crypto.Primitives.Garbling.Asymptotic
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Game.HiddenBit
import CslibFrontier.Crypto.Negligible.InversePolynomial
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for the abstract garbling-scheme framework

A trivial scheme on length-indexed bit strings is shown valid and well typed, an adversary with an
invalid query has advantage zero, a one-bit gate scheme with shape-only side information separates
`unitSideInfo` from `SideInfo.circ` on a valid `prv.ind` query, its inverters are verified, and the
reductions between indistinguishability and simulation security (`prv` and `obv`) are instantiated.
`prv.sim` with one simulator for every adversary (`Scheme.PrvSimSecureUniversal`) holds for the
trivial scheme, whose output is its input, and fails for `leakyScheme`, which garbles a function
with no output but whose garbled input is the input: an adversary that queries a uniform bit and
compares it with the first bit of `X` wins every real run and half of the simulated ones, whatever
the simulator. Importing both `CslibFrontier.Crypto.Primitives.Garbling.Basic` and
`CslibFrontier.Crypto.Primitives.Garbling.Foundations` also checks that the point-and-permute
circuit
garbling API and the abstract BHR12 framework coexist without namespace collisions.
-/

namespace CslibFrontierTests.Crypto.GarblingScheme

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Probability
open scoped NNReal

/-- The scheme on bit strings of a given length that garbles nothing: `ev` is the identity, the
garbled function and the encoding information are empty, and the decoding information records the
output length. -/
def identityScheme : Scheme ℕ :=
  ⟨id, id, id, fun _ x => x, fun _ _ _ _ => 0, fun _ n _ => ⟨[], [], List.replicate n false⟩,
    fun _ x => x, fun _ x => x, fun d y => if y.length = d.length then some y else none⟩

theorem eq_of_mem_support_identityScheme {k n : ℕ} {g : Scheme.Garbled}
    (hg : g ∈ (ProbComp.eval (identityScheme.garble k n)).support) :
    g = ⟨[], [], List.replicate n false⟩ := by
  obtain ⟨coins, -, rfl⟩ := identityScheme.mem_support_eval_garble_iff.mp hg
  rfl

theorem identityScheme_isValid : identityScheme.IsValid where
  length _ _ _ _ h _ hg _ hg' := by
    obtain ⟨hn, -, -⟩ := h; cases hn
    rw [eq_of_mem_support_identityScheme hg, eq_of_mem_support_identityScheme hg']
    exact ⟨rfl, rfl, rfl⟩
  nonDegenerate _ _ _ _ h _ _ := by obtain ⟨hn, -, -⟩ := h; cases hn; exact ⟨rfl, rfl⟩
  correct _ _ n x hx g hg := by
    have hx' : x.length = n := hx
    rw [eq_of_mem_support_identityScheme hg]
    change (if x.length = (List.replicate n false).length then some x else none) = some x
    simp [hx']

theorem identityScheme_wellTyped : identityScheme.WellTyped :=
  ⟨fun _ _ hx => hx, fun _ _ n g hg Y y hy => by
    rw [eq_of_mem_support_identityScheme hg] at hy
    change y ∈ (if Y.length = (List.replicate n false).length then some Y else none) at hy
    rw [List.length_replicate] at hy
    split_ifs at hy with h
    · exact Option.mem_some_iff.mp hy ▸ h
    · simp at hy⟩

example : identityScheme.decode [false, false] [true] = none := by decide

/-- An adversary asking for a function with one input on empty inputs. -/
def invalidAdversary : PrvIndAdversary ℕ Unit :=
  ⟨fun _ => pure (⟨⟨1, []⟩, ⟨1, []⟩⟩, ()), fun _ _ => pure true⟩

theorem prvIndAdvantage_invalidAdversary (k : ℕ) :
    prvIndAdvantage identityScheme (SideInfo.circ identityScheme) k invalidAdversary = 0 := by
  refine prvIndAdvantage_eq_zero_of_invalid _ _ _ _ fun pair st hmem => ?_
  simp only [invalidAdversary, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hmem
  obtain ⟨rfl, -⟩ := hmem
  decide

/-- A scheme over `Bool` (`false` = identity gate, `true` = negation gate on one-bit inputs). -/
def gateScheme : Scheme Bool :=
  ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun b x => x.map (fun bit => bit ^^ b),
    fun _ _ _ _ => 0, fun _ b _ => ⟨[b], [], [false]⟩, fun _ x => x,
    fun F x => x.map (fun bit => bit ^^ F.headD false),
    fun d y => if y.length = d.length then some y else none⟩

/-- Side information that reveals only the unit shape `(1, 1, 1)` and hides the gate bit. -/
def unitSideInfo : SideInfo Bool Unit := ⟨fun _ => (), fun _ => 1, fun _ => 1, fun _ => 1⟩

theorem unitSideInfo_compatible : unitSideInfo.Compatible gateScheme := fun _ => ⟨rfl, rfl, rfl⟩

/-- The constant inverter returning the identity gate `false`. -/
def invertUnit : Unit → Bool := fun _ => false

/-- The `ev`-inverter returning the query of the identity gate `false` on the target output `y`. -/
def evInvertUnit : Unit → List Bool → Query Bool := fun _ y => ⟨false, y⟩

theorem unitSideInfo_isInverter : unitSideInfo.IsInverter invertUnit := fun _ => rfl

theorem unitSideInfo_isEvInverter : unitSideInfo.IsEvInverter gateScheme evInvertUnit :=
  fun _ _ hx =>
    ⟨rfl, by simpa [gateScheme, evInvertUnit] using hx, by simp [gateScheme, evInvertUnit]⟩

example : prvIndValid gateScheme unitSideInfo ⟨⟨false, [true]⟩, ⟨true, [false]⟩⟩ := by decide

example :
    ¬ prvIndValid gateScheme (SideInfo.circ gateScheme) ⟨⟨false, [true]⟩, ⟨true, [false]⟩⟩ := by
  decide

example {σ : Type} (k : ℕ) (S : PrvSimulator Unit) (A : PrvIndAdversary Bool σ) :
    prvIndAdvantage gateScheme unitSideInfo k A ≤
      2 * prvSimAdvantage gateScheme unitSideInfo k S (prvIndToSim gateScheme unitSideInfo A) :=
  prvIndAdvantage_le_two_mul_prvSimAdvantage_prvIndToSim _ _ unitSideInfo_compatible k S A

example {σ : Type} (k : ℕ) (B : PrvSimAdversary Bool σ) :
    prvSimAdvantage gateScheme unitSideInfo k (prvSimFromInverter gateScheme k evInvertUnit) B ≤
      prvIndAdvantage gateScheme unitSideInfo k
        (prvSimToInd gateScheme unitSideInfo evInvertUnit B) :=
  prvSimAdvantage_prvSimFromInverter_le _ _ unitSideInfo_compatible unitSideInfo_isEvInverter k B

example {σ : Type} (k : ℕ) (S : ObvSimulator Unit) (A : ObvIndAdversary Bool σ) :
    obvIndAdvantage gateScheme unitSideInfo k A ≤
      2 * obvSimAdvantage gateScheme unitSideInfo k S (obvIndToSim gateScheme unitSideInfo A) :=
  obvIndAdvantage_le_two_mul_obvSimAdvantage_obvIndToSim _ _ unitSideInfo_compatible k S A

example {σ : Type} (k : ℕ) (B : ObvSimAdversary Bool σ) :
    obvSimAdvantage gateScheme unitSideInfo k (obvSimFromInverter gateScheme k invertUnit) B ≤
      obvIndAdvantage gateScheme unitSideInfo k
        (obvSimToInd gateScheme unitSideInfo invertUnit B) :=
  obvSimAdvantage_obvSimFromInverter_le _ _ unitSideInfo_compatible unitSideInfo_isInverter k B

/-! ### `prv.sim` with one simulator for every adversary -/

section Universal

open Turing.MultiTapeTM Probability

/-- The simulator for the trivial scheme: the output as the garbled input, with an empty garbled
function and decoding information of the output's length. -/
noncomputable def identitySim : ℕ → PrvSimulator ℕ :=
  fun _ y _ => pure ⟨[], y, List.replicate y.length false⟩

/-- **The trivial scheme satisfies `prv.sim` with one simulator**: its output is its input, so
`identitySim` writes the real view exactly. -/
theorem prvSimSecureUniversal_identityScheme :
    identityScheme.PrvSimSecureUniversal (SideInfo.circ identityScheme) encUnary encUnary := by
  refine ⟨identitySim, ?_, fun σ encσ B _ => ?_⟩
  · have h : ComputableInPolyTime (fun p : ℕ × List Bool × ℕ =>
        (⟨[], p.2.1, List.replicate p.2.1.length false⟩ : PrvView))
        (encPair encUnary (encPair encBits encUnary)) encPrvView := by
      polytime
    exact h.isPPTOn.congr fun ⟨_, _, _⟩ => rfl
  · refine negligible_of_eventually_le negligible_zero (Filter.Eventually.of_forall fun k => ?_)
    have heq : ProbComp.eval (prvSimExperiment identityScheme (SideInfo.circ identityScheme) k
        (identitySim k) (B k) false) =
        ProbComp.eval (prvSimExperiment identityScheme (SideInfo.circ identityScheme) k
          (identitySim k) (B k) true) := by
      simp only [prvSimExperiment, ProbComp.eval_bind, Bool.false_eq_true, ↓reduceIte]
      refine congrArg _ (funext fun p => ?_)
      by_cases hp : p.1.input.length = identityScheme.inLen p.1.fn
      · simp [hp, identitySim, Scheme.prvView, Scheme.garble, identityScheme]
      · simp only [hp, ↓reduceIte]
    simp only [prvSimAdvantage, Experiment.advantage, heq, Game.advantage_self]
    exact le_rfl

/-- A garbling scheme of functions with no output whose garbled input is the input itself: the
function `n` takes `n` bits and returns the empty word, and `En(e, x) = x`. It is correct. -/
def leakyScheme : Scheme ℕ where
  inLen := id
  outLen _ := 0
  size := id
  ev _ _ := []
  coinLen _ _ _ _ := 0
  gb _ _ _ := ⟨[], [], []⟩
  encode _ x := x
  evalGarbled _ _ := []
  decode _ _ := some []

theorem leakyScheme_correct : leakyScheme.Correct := fun _ _ _ _ _ _ _ => rfl

/-- The adversary against `leakyScheme`: query a uniform one-bit input of the function `1`, keep
it, and compare its bit with the first bit of the garbled input. -/
noncomputable def bitGuesser : ℕ → PrvSimAdversary ℕ (List Bool) := fun _ =>
  { choose := fun _ => do
      let w ← BitString.sampleList 1
      return (⟨1, w⟩, w)
    guess := fun w V => pure ((V.getD ⟨[], [], []⟩).input.getD 0 false == w.getD 0 false) }

theorem isPPT_bitGuesser :
    TwoStage.IsPPT encUnit (encQuery ℕ encUnary) (encOption encPrvView) encBool encBits
      bitGuesser where
  choose := by
    have h : ComputableInPolyTime (fun p : (ℕ × Unit) × List Bool => ((⟨1, p.2⟩ : Query ℕ), p.2))
        (encPair (encPair encUnary encUnit) encBits) (encPair (encQuery ℕ encUnary) encBits) := by
      polytime
    refine (IsPPTOn.of_seeded (count := fun _ : ℕ × Unit => 1) (.const 1) h).congr fun x => ?_
    simp only [bitGuesser, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure]
    exact (PMF.bind_pure_comp _ _).symm
  guess := by
    have hX : ComputableInPolyTime (fun p : ℕ × List Bool × Option PrvView =>
        (p.2.2.getD ⟨[], [], []⟩).input.getD 0 false)
        (encPair encUnary (encPair encBits (encOption encPrvView))) encBool := by
      fun_prop
    have hw : ComputableInPolyTime (fun p : ℕ × List Bool × Option PrvView => p.2.1.getD 0 false)
        (encPair encUnary (encPair encBits (encOption encPrvView))) encBool := by
      fun_prop
    exact ((ComputableInPolyTime.of_finite fun q : Bool × Bool => q.1 == q.2).comp
      (hX.prod hw)).isPPTOn.congr fun ⟨_, _, _⟩ => rfl

/-- Against every simulator, `bitGuesser` has `prv.sim` advantage `1 / 2`: it wins every real run,
and the simulated garbled input does not depend on the uniform bit. -/
theorem prvSimAdvantage_bitGuesser (S : PrvSimulator ℕ) (k : ℕ) :
    (prvSimAdvantage leakyScheme (SideInfo.circ leakyScheme) k S (bitGuesser k) : ℝ) = 1 / 2 := by
  have hsample : ProbComp.eval (BitString.sampleList 1) =
      (PMF.uniformOfFintype Bool).bind fun b => PMF.pure [b] := by
    rw [BitString.eval_sampleList, BitString.uniformList_succ, BitString.uniformList_zero]
    simp only [PMF.pure_map]
  have hreal : ProbComp.eval
      (prvSimExperiment leakyScheme (SideInfo.circ leakyScheme) k S (bitGuesser k) true) =
        PMF.pure true := by
    simp only [prvSimExperiment, bitGuesser, bind_pure_comp, List.getD_eq_getElem?_getD,
      leakyScheme, id_eq, ↓reduceIte, Scheme.prvView, Scheme.garble, Functor.map_map,
      Option.getD_some, Option.getD_none, List.length_nil, lt_self_iff_false, not_false_eq_true,
      getElem?_neg, Bool.false_beq, bind_map_left, BEq.rfl, ProbComp.eval_bind, hsample,
      PMF.bind_bind, PMF.pure_bind, List.length_cons, zero_add, ProbComp.eval_map,
      BitString.eval_sampleList, PMF.bind_const]
    exact PMF.map_const _ _
  have hsim : ProbComp.eval
      (prvSimExperiment leakyScheme (SideInfo.circ leakyScheme) k S (bitGuesser k) false) =
        (PMF.uniformOfFintype Bool).bind fun b =>
          ((ProbComp.eval (S [] 1)).map fun V => V.input.getD 0 false).map (· == b) := by
    simp [prvSimExperiment, bitGuesser, leakyScheme, hsample, PMF.map_comp, Function.comp_def,
      SideInfo.circ]
  rw [prvSimAdvantage, Experiment.advantage, hreal, hsim, Game.advantage_comm,
    Game.coe_advantage_pure_true_left]
  have h := Game.succProbability_uniform_bool_beq
    (fun _ => (ProbComp.eval (S [] 1)).map fun V => V.input.getD 0 false)
  rw [Game.coe_succProbability] at h
  rw [h]
  ring

/-- **`leakyScheme` is not `prv.sim` secure with one simulator**, with the function as side
information: the notion is not trivial. -/
theorem not_prvSimSecureUniversal_leakyScheme :
    ¬ leakyScheme.PrvSimSecureUniversal (SideInfo.circ leakyScheme) encUnary encUnary := by
  rintro ⟨S, -, h⟩
  refine not_negligible_of_eventually_ge (c := 1 / 2) (by norm_num) (Filter.Eventually.of_forall
    fun k => ?_) (h _ encBits bitGuesser isPPT_bitGuesser)
  rw [← NNReal.coe_le_coe, prvSimAdvantage_bitGuesser]
  norm_num

end Universal

/--
info: 'CslibFrontierTests.Crypto.GarblingScheme.unitSideInfo_isEvInverter' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unitSideInfo_isEvInverter

/-- info: 'Cslib.Crypto.Garbling.SideInfo.circ_isInverter' does not depend on any axioms -/
#guard_msgs in
#print axioms SideInfo.circ_isInverter

end CslibFrontierTests.Crypto.GarblingScheme
