/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

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
   `(2, 3)` Shamir secret sharing: `2`-resilience and `1`-resilience below threshold, strict
   expected utility loss (`< 4`) under a genuinely share-inspecting deviation (`sh = 0` in round
   `0`), and failure of pure Nash equilibrium above threshold (`p = 1 / 2`).
-/

public section

namespace CslibFrontierTests.RationalSecretSharing

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
  norm_num [testPrefs, SecretSharingPrefs.criticalStoppingProb]

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
  have hlearn :
      game3of3.learnedSet (ReconstructionGame.broadcastSet ![true, true, false]) = {2} := by
    ext j
    fin_cases j <;> decide
  have hne : ({2} : Finset (Fin 3)) ≠ Finset.univ := by decide
  refine ⟨hlearn, ?_, ?_⟩
  · dsimp only [ReconstructionGame.simultaneousGame]
    rw [hlearn]
    simp [SecretSharingPrefs.outcomeUtility, hne, game3of3, ReconstructionGame.allOfAll, testPrefs]
  · dsimp only [ReconstructionGame.simultaneousGame]
    rw [hlearn]
    simp [SecretSharingPrefs.outcomeUtility, game3of3, ReconstructionGame.allOfAll, testPrefs]

/-- In `2`-out-of-`4`, if only player `0` broadcasts (`![true, false, false, false]`), all three
non-broadcasters `{1, 2, 3}` combine their private share with `0`'s broadcast share to learn the
secret (`U⁺ = 10`), while broadcaster `0` fails to learn (`U⁻ = 0`). -/
example :
    let s : Fin 4 → Bool := ![true, false, false, false]
    game2of4.learnedSet (ReconstructionGame.broadcastSet s) = {1, 2, 3} ∧
      game2of4.simultaneousGame.payoff 0 s = 0 ∧
      game2of4.simultaneousGame.payoff 1 s = 10 := by
  have hlearn :
      game2of4.learnedSet (ReconstructionGame.broadcastSet ![true, false, false, false]) =
        {1, 2, 3} := by
    ext j
    fin_cases j <;> decide
  have hne : ({1, 2, 3} : Finset (Fin 4)) ≠ Finset.univ := by decide
  have hmem : (1 : Fin 4) ∈ ({1, 2, 3} : Finset (Fin 4)) := by decide
  have hnmem : (0 : Fin 4) ∉ ({1, 2, 3} : Finset (Fin 4)) := by decide
  refine ⟨hlearn, ?_, ?_⟩
  · dsimp only [ReconstructionGame.simultaneousGame]
    rw [hlearn, SecretSharingPrefs.outcomeUtility_of_not_mem _ hnmem]
    rfl
  · dsimp only [ReconstructionGame.simultaneousGame]
    rw [hlearn, SecretSharingPrefs.outcomeUtility_of_mem_of_ne_univ _ hmem hne]
    rfl

/-- One round of `IDoWDS` on simultaneous `2`-out-of-`4` broadcast eliminates `true` for every
player, and the unique surviving profile `fun _ => false` gives every player utility `0`. -/
example :
    game2of4.simultaneousGame.idowdsIter 1 = (fun _ => {false}) ∧
      ∀ i : Fin 4, game2of4.simultaneousGame.payoff i (fun _ => false) = 0 := by
  refine ⟨game2of4.idowdsIter_simultaneousGame_one, fun i => ?_⟩
  simp [ReconstructionGame.simultaneousGame, game2of4, testPrefs]

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
    norm_num [game3of3, ReconstructionGame.allOfAll, testPrefs,
      SecretSharingPrefs.criticalStoppingProb]
  have hstrict := game3of3.honest_isStrictPureNash_geometricStageGame hp0 hp
  exact ⟨hstrict,
    (PayoffGame.isPureNash_toCostGame_iff _).mpr hstrict.isPureNash,
    game3of3.idowdsIter_geometricStageGame_one hp0 hp rfl⟩

/-- At the exact critical boundary `p = 2 / 5`, honest broadcast is a pure Nash equilibrium of
`game3of3.geometricStageGame (2 / 5)`, but **not** a strict pure Nash equilibrium because
unilateral withholding achieves `(2 / 5) * 10 + (3 / 5) * 0 = 4 = U`. -/
example :
    (game3of3.geometricStageGame (2 / 5)).IsPureNash (fun _ => true) ∧
      ¬ (game3of3.geometricStageGame (2 / 5)).IsStrictPureNash (fun _ => true) := by
  have hp : (2 / 5 : ℝ) ≤ game3of3.prefs.criticalStoppingProb := by
    norm_num [game3of3, ReconstructionGame.allOfAll, testPrefs,
      SecretSharingPrefs.criticalStoppingProb]
  refine ⟨game3of3.honest_isPureNash_geometricStageGame (by norm_num) hp, fun hstrict => ?_⟩
  have hlt := hstrict 0 false Bool.false_ne_true
  have hB :
      ReconstructionGame.broadcastSet (Function.update (fun _ : Fin 3 => true) 0 false) = {1, 2} :=
    by ext j; fin_cases j <;> decide
  have hL : game3of3.learnedSet {1, 2} = {0} := by
    ext j; fin_cases j <;> decide
  have hnot_all : ¬ ∀ j : Fin 3, Function.update (fun _ : Fin 3 => true) 0 false j = true := by
    decide
  have hall_t : ∀ _ : Fin 3, true = true := fun _ => rfl
  have hne : ({0} : Finset (Fin 3)) ≠ Finset.univ := by decide
  dsimp only [ReconstructionGame.geometricStageGame] at hlt
  split_ifs at hlt
  rw [hB, hL,
    SecretSharingPrefs.outcomeUtility_of_mem_of_ne_univ _ (Finset.mem_singleton_self 0) hne] at hlt
  norm_num [game3of3, ReconstructionGame.allOfAll, testPrefs] at hlt

/-- Above threshold (`p = 1 / 2 > 2 / 5`), honest broadcast is NOT a pure Nash equilibrium of
`game3of3.geometricStageGame (1 / 2)`. -/
example : ¬ (game3of3.geometricStageGame (1 / 2)).IsPureNash (fun _ => true) := by
  rw [game3of3.honest_isPureNash_geometricStageGame_iff (by norm_num) rfl]
  norm_num [game3of3, ReconstructionGame.allOfAll, testPrefs,
    SecretSharingPrefs.criticalStoppingProb]

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
`2`-coalitionally resilient (`IsCoalitionProofUpTo 2`), and is a pure Nash equilibrium of both
`toPayoffGame` and `toPayoffGame.toCostGame`. -/
example :
    proto3of3Good.toPayoffGame.payoff 0 GeometricProtocol.honestProfile = 4 ∧
      proto3of3Good.toPayoffGame.IsCoalitionProofUpTo 2 GeometricProtocol.honestProfile ∧
      proto3of3Good.toPayoffGame.toCostGame.IsPureNash GeometricProtocol.honestProfile := by
  have hp : (1 / 4 : ℝ) ≤ testPrefs.criticalStoppingProb := by
    norm_num [testPrefs, SecretSharingPrefs.criticalStoppingProb]
  have hcoal :
      proto3of3Good.toPayoffGame.IsCoalitionProofUpTo 2 GeometricProtocol.honestProfile :=
    GeometricProtocol.ofShamir_honestProfile_isCoalitionProofUpTo testPrefs shamirParams3of3 3 0
      (1 / 4) (by norm_num) (by norm_num) hp
  refine ⟨?_, hcoal, (PayoffGame.isPureNash_toCostGame_iff _).mpr (hcoal.isPureNash (by decide))⟩
  simp [proto3of3Good, testPrefs]

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
    norm_num [proto3of3Good, testPrefs, SecretSharingPrefs.criticalStoppingProb]
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
        dsimp only [d, GeometricProtocol.roundBroadcastDist]
        rw [ne_eq, PMF.apply_eq_zero_iff, PMF.mem_support_map_iff, not_not]
        refine ⟨0, ?_, ?_⟩
        · simp [proto3of3Good, uniformOfFintype]
        · funext j
          fin_cases j
          · simp [σ, σ₀, proto3of3Good, shamirUniformAccessScheme, shamirAccessSchemeOf, b₀]
          · simp [σ, GeometricProtocol.honestProfile, b₀]
          · simp [σ, GeometricProtocol.honestProfile, b₀]
      exact ENNReal.toReal_pos hne0 (PMF.apply_ne_top d b₀)
    have hsum := sum_toReal d
    have htwo :
        (d (fun _ => true)).toReal + (d b₀).toReal ≤ ∑ b : Fin 3 → Bool, (d b).toReal := by
      rw [← Finset.sum_pair (f := fun b => (d b).toReal) hb_ne.symm]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => ENNReal.toReal_nonneg
    have hcont : proto3of3Good.roundContinueProb σ 0 = (d (fun _ => true)).toReal := rfl
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
  norm_num [proto3of3TooFast, testPrefs, SecretSharingPrefs.criticalStoppingProb]

/-- In the `(2, 3)` Shamir geometric-stopping protocol `proto2of3Good` (`p = 1 / 3 ≤ 2 / 5`),
`honestProfile` is `1`-coalitionally resilient (`IsCoalitionProofUpTo 1`) and therefore a pure Nash
equilibrium. -/
example :
    proto2of3Good.toPayoffGame.IsCoalitionProofUpTo 1 GeometricProtocol.honestProfile ∧
      proto2of3Good.toPayoffGame.IsPureNash GeometricProtocol.honestProfile := by
  have hp : (1 / 3 : ℝ) ≤ testPrefs.criticalStoppingProb := by
    norm_num [testPrefs, SecretSharingPrefs.criticalStoppingProb]
  have hcoal :
      proto2of3Good.toPayoffGame.IsCoalitionProofUpTo 1 GeometricProtocol.honestProfile :=
    GeometricProtocol.ofShamir_honestProfile_isCoalitionProofUpTo testPrefs shamirParams2of3 4 1
      (1 / 3) (by norm_num) (by norm_num) hp
  exact ⟨hcoal, hcoal.isPureNash (by decide)⟩

end CslibFrontierTests.RationalSecretSharing
