/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.RationalCrypto.SecretSharing
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic.NormNum

/-!
# Tests for Rational Secret Sharing

Concrete finite witnesses for `Cslib.GameTheory.RationalCrypto`:

1. Concrete preference parameters `U⁺ = 10 > U = 4 > U⁻ = 0` with critical stopping probability
   `criticalStoppingProb = 2 / 5`.
2. Concrete `3`-out-of-`3` (`Fin 3`) and `2`-out-of-`4` (`Fin 4`) reconstruction outcomes, showing
   pivotal exclusivity payoffs (`10` vs `4` vs `0`) and Halpern–Teague `IDoWDS` collapse across
   single-round simultaneous broadcast, `4`-round uniform-ramp gradual release (including
   intermediate backward-induction horizons), and `3`-round known-final-round protocols.
3. Sharpness of the stage-game geometric stopping threshold `p = 2 / 5` on `3`-out-of-`3`:
   strict pure Nash equilibrium and `IDoWDS = {true}` at `p = 1 / 4`, non-strict pure Nash
   equilibrium at the boundary `p = 2 / 5`, and failure of Nash equilibrium at `p = 1 / 2`.
4. Concrete cryptographic `GeometricProtocol.ofShamir` instances over `ZMod 5` for `(3, 3)` and
   `(2, 3)` Shamir secret sharing: `2`-resilience and `1`-resilience against share-pooling joint
   coalitions (`IsJointCoalitionProofUpTo`), strict expected utility loss (`< 4`) under a genuinely
   share-inspecting deviation (`sh = 0` in round `0`), concrete 2-party coalition share-pooling
   deviation achieving `5 > 4` at `p = 1 / 2`, and `≤ 4` below threshold at `p = 1 / 4`.
-/

public section

namespace CslibFrontierTests.GameTheory.RationalSecretSharing

open Cslib.Crypto.Protocols.SecretSharing
open Cslib.GameTheory
open Cslib.GameTheory.RationalCrypto
open Cslib.Probability Cslib.Probability.PMF

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### 1. Concrete preference levels and critical stopping probability -/

/-- Canonical finite test preferences `U⁺ = 10 > U = 4 > U⁻ = 0`, giving threshold `2 / 5`. -/
def testPrefs : SecretSharingPrefs where
  uPlus := 10
  uAll := 4
  uMinus := 0
  uMinus_lt_uAll := by norm_num
  uAll_lt_uPlus := by norm_num

example : testPrefs.criticalStoppingProb = 2 / 5 := by
  norm_num [testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]

/-- `3`-out-of-`3` rational secret-sharing game on `Fin 3`. -/
def game3of3 : ReconstructionGame (Fin 3) :=
  ReconstructionGame.allOfAll (Fin 3) testPrefs (by decide)

/-- `2`-out-of-`4` rational secret-sharing game on `Fin 4`. -/
def game2of4 : ReconstructionGame (Fin 4) where
  prefs := testPrefs
  threshold := 2
  two_le_threshold := by decide
  threshold_le_card := by decide

/-! ### 2. Pivotal outcomes and Halpern–Teague deterministic impossibility -/

/-- In `3`-out-of-`3`, if players `0` and `1` broadcast while player `2` withholds, only player `2`
reconstructs the secret (`learnedSet = {2}`), earning `U⁺ = 10` while `0` and `1` get `U⁻ = 0`. -/
example :
    let s : Fin 3 → Bool := ![true, true, false]
    game3of3.learnedSet (ReconstructionGame.broadcastSet s) = {2} ∧
      game3of3.simultaneousGame.payoff 2 s = 10 ∧
      game3of3.simultaneousGame.payoff 0 s = 0 := by
  have hB : ReconstructionGame.broadcastSet ![true, true, false] = {0, 1} := by
    ext j
    simp only [ReconstructionGame.mem_broadcastSet_iff]
    fin_cases j <;> decide
  have hlearn :
      game3of3.learnedSet (ReconstructionGame.broadcastSet ![true, true, false]) = {2} := by
    ext j
    simp only [ReconstructionGame.mem_learnedSet_iff, hB, game3of3,
      ReconstructionGame.allOfAll_threshold, Fintype.card_fin]
    fin_cases j <;> decide
  have hne : ({2} : Finset (Fin 3)) ≠ Finset.univ := by decide
  refine ⟨hlearn, ?_, ?_⟩
  · rw [ReconstructionGame.simultaneousGame_payoff, hlearn,
      SecretSharingPrefs.outcomeUtility_of_mem_of_ne_univ _ (Finset.mem_singleton_self 2) hne]
    simp [game3of3, ReconstructionGame.allOfAll_prefs, testPrefs]
  · rw [ReconstructionGame.simultaneousGame_payoff, hlearn,
      SecretSharingPrefs.outcomeUtility_of_not_mem _ (by decide)]
    simp [game3of3, ReconstructionGame.allOfAll_prefs, testPrefs]

/-- In `2`-out-of-`4`, if only player `0` broadcasts (`![true, false, false, false]`), all three
non-broadcasters `{1, 2, 3}` combine their private share with `0`'s broadcast share to learn the
secret (`U⁺ = 10`), while broadcaster `0` fails to learn (`U⁻ = 0`). -/
example :
    let s : Fin 4 → Bool := ![true, false, false, false]
    game2of4.learnedSet (ReconstructionGame.broadcastSet s) = {1, 2, 3} ∧
      game2of4.simultaneousGame.payoff 0 s = 0 ∧
      game2of4.simultaneousGame.payoff 1 s = 10 := by
  have hB : ReconstructionGame.broadcastSet ![true, false, false, false] = {0} := by
    ext j
    simp only [ReconstructionGame.mem_broadcastSet_iff]
    fin_cases j <;> decide
  have hlearn :
      game2of4.learnedSet (ReconstructionGame.broadcastSet ![true, false, false, false]) =
        {1, 2, 3} := by
    ext j
    simp only [ReconstructionGame.mem_learnedSet_iff, hB, game2of4]
    fin_cases j <;> decide
  have hne : ({1, 2, 3} : Finset (Fin 4)) ≠ Finset.univ := by decide
  have hmem : (1 : Fin 4) ∈ ({1, 2, 3} : Finset (Fin 4)) := by decide
  have hnmem : (0 : Fin 4) ∉ ({1, 2, 3} : Finset (Fin 4)) := by decide
  refine ⟨hlearn, ?_, ?_⟩
  · rw [ReconstructionGame.simultaneousGame_payoff, hlearn,
      SecretSharingPrefs.outcomeUtility_of_not_mem _ hnmem]
    simp [game2of4, testPrefs]
  · rw [ReconstructionGame.simultaneousGame_payoff, hlearn,
      SecretSharingPrefs.outcomeUtility_of_mem_of_ne_univ _ hmem hne]
    simp [game2of4, testPrefs]

/-- One round of `IDoWDS` on simultaneous `2`-out-of-`4` broadcast eliminates `true` for every
player, matches `CostGame.idowdsSeq` on `toCostGame`, and the surviving profile yields utility `0`.
-/
example :
    game2of4.simultaneousGame.idowdsIter 1 = (fun _ => {false}) ∧
      game2of4.simultaneousGame.toCostGame.idowdsSeq 1 = (fun _ => {false}) ∧
      ∀ i : Fin 4, game2of4.simultaneousGame.payoff i (fun _ => false) = 0 := by
  refine ⟨game2of4.idowdsIter_simultaneousGame_one, ?_, fun i => ?_⟩
  · rw [← PayoffGame.idowdsIter_eq_toCostGame_idowdsSeq]
    exact game2of4.idowdsIter_simultaneousGame_one
  · simp [ReconstructionGame.simultaneousGame_payoff, game2of4, testPrefs]

/-- Backward-induction `IDoWDS` on the `4`-round uniform-ramp game on `Fin 3`: after `2` rounds of
deletion only cutoffs `{0, 1, 2}` survive, and after `4` rounds only `{0}` survives. -/
example :
    (game3of3.uniformRampGame 4).idowdsIter 2 =
        (fun _ => { r : Fin 5 | r.val ≤ 2 }) ∧
      (game3of3.uniformRampGame 4).idowdsIter 4 = fun _ => {0} :=
  ⟨PayoffGame.idowdsIter_eq_le_sub (game3of3.hasBackwardInductionDominance_uniformRampGame 4)
      (by decide),
    game3of3.idowdsIter_uniformRampGame 4⟩

/-- In the `3`-round known-final-round `2`-out-of-`4` game, every profile surviving a single step
of `IDoWDS` yields utility `0` (`U⁻`) to every player. -/
example (s : Fin 4 → Fin 4)
    (hs : ∀ j, s j ∈ (game2of4.knownHorizonGame 3).idowdsIter 1 j) (i : Fin 4) :
    (game2of4.knownHorizonGame 3).payoff i s = 0 :=
  game2of4.payoff_knownHorizonGame_eq_uMinus_of_mem_idowdsIter_one (by decide) hs i

/-! ### 3. Stage-game threshold sharpness (`p = 1/4`, `p = 2/5`, `p = 1/2`) -/

/-- Below threshold (`p = 1 / 4 < 2 / 5`), honest broadcast in `game3of3` is a strict pure Nash
equilibrium, a `CostGame` pure Nash equilibrium, and the unique survivor of `IDoWDS`. -/
example :
    (game3of3.geometricStageGame (1 / 4)).IsStrictPureNash (fun _ => true) ∧
      (game3of3.geometricStageGame (1 / 4)).toCostGame.IsPureNash (fun _ => true) ∧
      (game3of3.geometricStageGame (1 / 4)).idowdsIter 1 = fun _ => {true} := by
  have hp0 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hp : (1 / 4 : ℝ) < game3of3.prefs.criticalStoppingProb := by
    norm_num [game3of3, testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]
  have hstrict := game3of3.honest_isStrictPureNash_geometricStageGame hp0 hp
  exact ⟨hstrict,
    (PayoffGame.isPureNash_toCostGame_iff _).mpr hstrict.isPureNash,
    game3of3.idowdsIter_geometricStageGame_one hp0 hp
      (by simp [game3of3, ReconstructionGame.allOfAll_threshold])⟩

/-- At the exact critical boundary `p = 2 / 5`, honest broadcast is a pure Nash equilibrium of
`game3of3.geometricStageGame (2 / 5)`, but **not** a strict pure Nash equilibrium because
unilateral withholding achieves `(2 / 5) * 10 + (3 / 5) * 0 = 4 = U`. -/
example :
    (game3of3.geometricStageGame (2 / 5)).IsPureNash (fun _ => true) ∧
      ¬ (game3of3.geometricStageGame (2 / 5)).IsStrictPureNash (fun _ => true) := by
  have hp : (2 / 5 : ℝ) ≤ game3of3.prefs.criticalStoppingProb := by
    norm_num [game3of3, testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]
  refine ⟨game3of3.honest_isPureNash_geometricStageGame (by norm_num) hp, fun hstrict => ?_⟩
  have hlt := hstrict 0 false Bool.false_ne_true
  have hB :
      ReconstructionGame.broadcastSet (Function.update (fun _ : Fin 3 => true) 0 false) = {1, 2} :=
    by
    ext j
    simp only [ReconstructionGame.mem_broadcastSet_iff]
    fin_cases j <;> decide
  have hL : game3of3.learnedSet {1, 2} = {0} := by
    ext j
    simp only [ReconstructionGame.mem_learnedSet_iff, game3of3,
      ReconstructionGame.allOfAll_threshold, Fintype.card_fin]
    fin_cases j <;> decide
  have hnot_all : ¬ ∀ j : Fin 3, Function.update (fun _ : Fin 3 => true) 0 false j = true := by
    decide
  have hne : ({0} : Finset (Fin 3)) ≠ Finset.univ := by decide
  have htrue : ∀ _ : Fin 3, True := fun _ => trivial
  simp_rw [ReconstructionGame.geometricStageGame_payoff] at hlt
  split_ifs at hlt
  rw [hB, hL,
    SecretSharingPrefs.outcomeUtility_of_mem_of_ne_univ _ (Finset.mem_singleton_self 0) hne]
    at hlt
  norm_num [game3of3, ReconstructionGame.allOfAll_prefs, testPrefs] at hlt

/-- Above threshold (`p = 1 / 2 > 2 / 5`), honest broadcast is NOT a pure Nash equilibrium of
`game3of3.geometricStageGame (1 / 2)`. -/
example : ¬ (game3of3.geometricStageGame (1 / 2)).IsPureNash (fun _ => true) := by
  rw [game3of3.honest_isPureNash_geometricStageGame_iff (by norm_num)
    (by simp [game3of3, ReconstructionGame.allOfAll_threshold])]
  norm_num [game3of3, testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]

/-! ### 4. Cryptographic `GeometricProtocol.ofShamir` witnesses over `ZMod 5` -/

/-- `(3, 3)` Shamir parameters over `ZMod 5` (degree `2`, evaluation points `1, 2, 3`). -/
def shamirParams3of3 : Shamir.Params (ZMod 5) (Fin 3) where
  threshold := 2
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 5)
  point_injective := by decide
  point_nonzero := by decide

/-- `(2, 3)` Shamir parameters over `ZMod 5` (degree `1`, evaluation points `1, 2, 3`). -/
def shamirParams2of3 : Shamir.Params (ZMod 5) (Fin 3) where
  threshold := 1
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 5)
  point_injective := by decide
  point_nonzero := by decide

/-- Concrete `(3, 3)` Shamir geometric-stopping protocol over `ZMod 5` with `p = 1 / 4`, genuine
secret `3`, and dummy value `0`. -/
noncomputable def proto3of3Good :
    GeometricProtocol (Fin 3) (ZMod 5) (Shamir.Randomness shamirParams3of3) (fun _ => ZMod 5) :=
  GeometricProtocol.ofShamir testPrefs shamirParams3of3 3 0 (1 / 4) (by norm_num) (by norm_num)

/-- Concrete `(3, 3)` Shamir geometric-stopping protocol over `ZMod 5` with `p = 1 / 2 > 2 / 5`. -/
noncomputable def proto3of3TooFast :
    GeometricProtocol (Fin 3) (ZMod 5) (Shamir.Randomness shamirParams3of3) (fun _ => ZMod 5) :=
  GeometricProtocol.ofShamir testPrefs shamirParams3of3 3 0 (1 / 2) (by norm_num) (by norm_num)

/-- Concrete `(2, 3)` Shamir geometric-stopping protocol over `ZMod 5` with `p = 1 / 3 ≤ 2 / 5`. -/
noncomputable def proto2of3Good :
    GeometricProtocol (Fin 3) (ZMod 5) (Shamir.Randomness shamirParams2of3) (fun _ => ZMod 5) :=
  GeometricProtocol.ofShamir testPrefs shamirParams2of3 4 1 (1 / 3) (by norm_num) (by norm_num)

/-- In `proto3of3Good` (`p = 1 / 4 ≤ 2 / 5`), `honestProfile` achieves expected utility `4`, is
`2`-resilient against joint share-pooling coalitions (`IsJointCoalitionProofUpTo 2`), `2`-resilient
against independent deviations (`IsCoalitionProofUpTo 2`), and is a `CostGame` pure Nash
equilibrium. -/
example :
    proto3of3Good.toPayoffGame.payoff 0 GeometricProtocol.honestProfile = 4 ∧
      proto3of3Good.IsJointCoalitionProofUpTo 2 ∧
      proto3of3Good.toPayoffGame.IsCoalitionProofUpTo 2 GeometricProtocol.honestProfile ∧
      proto3of3Good.toPayoffGame.toCostGame.IsPureNash GeometricProtocol.honestProfile := by
  have hp : (1 / 4 : ℝ) ≤ testPrefs.criticalStoppingProb := by
    norm_num [testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]
  have hjoint : proto3of3Good.IsJointCoalitionProofUpTo 2 :=
    GeometricProtocol.ofShamir_honestProfile_isJointCoalitionProofUpTo testPrefs shamirParams3of3
      3 0 (1 / 4) (by norm_num) (by norm_num) hp
  have hcoal :
      proto3of3Good.toPayoffGame.IsCoalitionProofUpTo 2 GeometricProtocol.honestProfile :=
    hjoint.toPayoffGame (by decide)
  refine ⟨?_, hjoint, hcoal,
    (PayoffGame.isPureNash_toCostGame_iff _).mpr (hcoal.isPureNash (by decide))⟩
  simp [proto3of3Good, testPrefs]

/-- **Concrete `2`-party coalition share-pooling deviation**: in `3`-out-of-`3` Shamir sharing, when
coalition `{0, 1}` pools its shares and withholds together in round `0` (`fun _ _ _ => false`)
while honest party `2` broadcasts, `{0, 1}` learns exclusively when round `0` is genuine:
- in `proto3of3TooFast` (`p = 1 / 2 > 2 / 5`), member `0` achieves `coalitionPayoff = 5 > 4`,
  refuting `IsJointCoalitionProofUpTo 2`;
- in `proto3of3Good` (`p = 1 / 4 ≤ 2 / 5`), member `0` obtains at most `4`. -/
example :
    let C : Finset (Fin 3) := {0, 1}
    let τC : GeometricProtocol.CoalitionStrategy (Share := fun _ : Fin 3 => ZMod 5) C :=
      fun _ _ _ => false
    proto3of3TooFast.coalitionPayoff C τC 0 = 5 ∧
      4 < proto3of3TooFast.coalitionPayoff C τC 0 ∧
      ¬ proto3of3TooFast.IsJointCoalitionProofUpTo 2 ∧
      proto3of3Good.coalitionPayoff C τC 0 ≤ 4 := by
  intro C τC
  have hC_ne : C.Nonempty := ⟨0, by decide⟩
  have hC_univ : C ≠ Finset.univ := by decide
  have hOutFast : ¬ proto3of3TooFast.scheme.access.authorized (Finset.univ \ C) := by
    simp only [proto3of3TooFast, GeometricProtocol.ofShamir_scheme,
      shamirUniformAccessScheme_access, shamirAccessStructure, shamirParams3of3,
      AccessStructure.threshold_authorized_iff]
    decide
  have hpayFast : proto3of3TooFast.coalitionPayoff C τC 0 = 5 := by
    rw [proto3of3TooFast.coalitionPayoff_const_false hC_ne hC_univ hOutFast (by decide)]
    norm_num [proto3of3TooFast, testPrefs]
  have hnotJoint : ¬ proto3of3TooFast.IsJointCoalitionProofUpTo 2 := by
    have hthresh : proto3of3TooFast.scheme.access = AccessStructure.threshold (Fin 3) 3 := by
      simp [proto3of3TooFast, shamirAccessStructure, shamirParams3of3]
    rw [proto3of3TooFast.honestProfile_isJointCoalitionProofUpTo_iff (by decide) (by decide)
      hthresh]
    norm_num [proto3of3TooFast, testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]
  have hpGood : (1 / 4 : ℝ) ≤ testPrefs.criticalStoppingProb := by
    norm_num [testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]
  have hjointGood : proto3of3Good.IsJointCoalitionProofUpTo 2 :=
    GeometricProtocol.ofShamir_honestProfile_isJointCoalitionProofUpTo testPrefs shamirParams3of3
      3 0 (1 / 4) (by norm_num) (by norm_num) hpGood
  have hpayGood : proto3of3Good.coalitionPayoff C τC 0 ≤ 4 := by
    simpa [proto3of3Good, testPrefs] using hjointGood C (by decide) τC 0 (by decide)
  refine ⟨hpayFast, by linarith, hnotJoint, hpayGood⟩

/-- Share-inspecting deviation in `proto3of3Good`: player `0` inspects its `ZMod 5` share in round
`0` and withholds iff that share is `0` (`fun r sh => decide (r ≠ 0 ∨ sh ≠ 0)`). Because Shamir
shares hit `0` with positive probability in round `0`, player `0`'s infinite-horizon expected
utility is strictly less than `4`. -/
example :
    let σ₀ : GeometricProtocol.Strategy (Share := fun _ : Fin 3 => ZMod 5) 0 :=
      fun r sh => decide (r ≠ 0 ∨ sh ≠ 0)
    proto3of3Good.toPayoffGame.payoff 0
        (Function.update GeometricProtocol.honestProfile 0 σ₀) < 4 := by
  intro σ₀
  have hp : proto3of3Good.stopProb < proto3of3Good.prefs.criticalStoppingProb := by
    norm_num [proto3of3Good, testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]
  have hunauth : ¬ proto3of3Good.scheme.access.authorized ({0} : Finset (Fin 3)) := by
    simp [proto3of3Good, Shamir.authorized, shamirParams3of3]
  have hwithhold :
      0 < 1 - proto3of3Good.roundContinueProb
          (Function.update GeometricProtocol.honestProfile 0 σ₀) 0 := by
    set σ := Function.update GeometricProtocol.honestProfile 0 σ₀
    set d := proto3of3Good.roundBroadcastDist σ 0 proto3of3Good.dummy
    let b₀ : Fin 3 → Bool := Function.update (fun _ => true) 0 false
    have hb_ne : b₀ ≠ (fun _ => true) :=
      fun h => Bool.false_ne_true (by simpa [b₀] using congrFun h 0)
    have hpos_b₀ : 0 < (d b₀).toReal := by
      have hne0 : d b₀ ≠ 0 := by
        dsimp only [d]
        rw [GeometricProtocol.roundBroadcastDist_eq_map, ne_eq, PMF.apply_eq_zero_iff,
          PMF.mem_support_map_iff, not_not]
        refine ⟨0, ?_, ?_⟩
        · simp [proto3of3Good, uniformOfFintype]
        · funext j
          fin_cases j
          · simp [σ, σ₀, proto3of3Good, shamirUniformAccessScheme, shamirAccessSchemeOf, b₀]
          · simp [σ, b₀]
          · simp [σ, b₀]
      exact ENNReal.toReal_pos hne0 (PMF.apply_ne_top d b₀)
    have hsum := sum_toReal d
    have htwo :
        (d (fun _ => true)).toReal + (d b₀).toReal ≤ ∑ b : Fin 3 → Bool, (d b).toReal := by
      rw [← Finset.sum_pair (f := fun b => (d b).toReal) hb_ne.symm]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => ENNReal.toReal_nonneg
    have hcont : proto3of3Good.roundContinueProb σ 0 = (d (fun _ => true)).toReal :=
      proto3of3Good.roundContinueProb_eq σ 0
    linarith
  have hlt := proto3of3Good.payoff_lt_uAll_of_withholdProb_pos hp hunauth ⟨0, hwithhold⟩
  simpa [proto3of3Good, testPrefs] using hlt

/-- Above threshold (`p = 1 / 2 > 2 / 5`), `honestProfile` is NOT a pure Nash equilibrium of the
`(3, 3)` Shamir geometric-stopping game `proto3of3TooFast`. -/
example : ¬ proto3of3TooFast.toPayoffGame.IsPureNash GeometricProtocol.honestProfile := by
  have hall : proto3of3TooFast.scheme.access = AccessStructure.all (Fin 3) := by
    simp [proto3of3TooFast, shamirAccessStructure, shamirParams3of3,
      AccessStructure.all_eq_threshold]
  rw [proto3of3TooFast.honestProfile_isPureNash_iff hall (by decide)]
  norm_num [proto3of3TooFast, testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]

/-- In the `(2, 3)` Shamir geometric-stopping protocol `proto2of3Good` (`p = 1 / 3 ≤ 2 / 5`),
`honestProfile` is `1`-resilient against joint share-pooling coalitions
(`IsJointCoalitionProofUpTo 1`) and therefore `1`-coalitionally resilient (`IsCoalitionProofUpTo 1`)
and a pure Nash equilibrium. -/
example :
    proto2of3Good.IsJointCoalitionProofUpTo 1 ∧
      proto2of3Good.toPayoffGame.IsCoalitionProofUpTo 1 GeometricProtocol.honestProfile ∧
      proto2of3Good.toPayoffGame.IsPureNash GeometricProtocol.honestProfile := by
  have hp : (1 / 3 : ℝ) ≤ testPrefs.criticalStoppingProb := by
    norm_num [testPrefs, SecretSharingPrefs.criticalStoppingProb_eq]
  have hjoint : proto2of3Good.IsJointCoalitionProofUpTo 1 :=
    GeometricProtocol.ofShamir_honestProfile_isJointCoalitionProofUpTo testPrefs shamirParams2of3
      4 1 (1 / 3) (by norm_num) (by norm_num) hp
  have hcoal :
      proto2of3Good.toPayoffGame.IsCoalitionProofUpTo 1 GeometricProtocol.honestProfile :=
    hjoint.toPayoffGame (by decide)
  exact ⟨hjoint, hcoal, hcoal.isPureNash (by decide)⟩

end CslibFrontierTests.GameTheory.RationalSecretSharing
