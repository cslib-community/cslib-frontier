/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.GameTheory.Polymatrix.Basic
public import CslibFrontier.GameTheory.Strategic.PotentialCharacterization
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for potential game characterizations and polymatrix games

Concrete checked witnesses and counterexamples exercising the public API of
`CslibFrontier.GameTheory.Strategic.PotentialCharacterization` and
`CslibFrontier.GameTheory.Polymatrix.Basic`:

1. **Weighted vs. exact potential separation**: a `2 × 2` game with positive weights `w = (1, 2)`
   that has a `w`-potential (and whose mixed extension has a `w`-potential by Lemma 2.10), has the
   FIP and a pure Nash equilibrium, yet fails `FourCycleZero` and therefore admits **no** exact
   potential.
2. **Monderer–Shapley `G₁` counterexample ([MondererShapley1996], p. 129) vs. Corollary 2.6**:
   `msCounterexampleG1` has an explicit generalized ordinal potential (hence `HasFIP`), yet admits
   **no** ordinal potential because of a single unilateral cost tie, demonstrating sharpness of
   `exists_isOrdinalPotential_of_hasFIP` (Corollary 2.6, p. 130).
3. **Theorem 2.8 & Corollary 2.9**: explicit length-`4` simple closed unilateral path on Matching
   Pennies with nonzero path integral `pathIntegral = 8 ≠ 0` (ruling out any exact potential),
   plus explicit `potentialOfBase` (`potentialOfBase_self`) and `IsCoordination` + `IsDummy`
   decomposition on Prisoner's Dilemma ([MondererShapley1996], p. 128).
4. **3-player polymatrix games and `BimatrixGame` embedding**:
   * symmetric 3-player coordination / cut game with exact `edgePotential`, `HasFIP`,
     social-cost-optimal pure Nash equilibrium (`PoS = 1`), and uniform `(1/2, 1/2)` mixed Nash
     equilibrium checked via `deviationCost_toCostGame`, `expectedCost_toCostGame`, and
     `isMixedNash_toCostGame_iff`;
   * `PolymatrixGame.ofBimatrixGame` compatibility with `BimatrixGame.toCostGame`;
   * **asymmetric** 3-player polymatrix game (`¬ IsSymmetric`) whose skew-symmetric part is
     separable (`IsSeparableSkew`), proving it still admits an exact potential;
   * baseline-zero-normalized asymmetric polymatrix game admitting **no** exact potential.
-/

@[expose] public section

namespace CslibFrontierTests.GameTheory.PotentialPolymatrix

open Cslib.GameTheory Function

/-! ### 1. Weighted potential game with no exact potential, plus Lemma 2.10 -/

/-- Two-player binary cost game where player `false` pays `Φ` and player `true` pays `2 * Φ`
for `Φ(a, b) = if a == b then 0 else 1`. -/
def weightedOnlyGame : CostGame Bool (fun _ => Bool) where
  cost
    | false => fun s => if s false == s true then 0 else 1
    | true => fun s => if s false == s true then 0 else 2

/-- Common mismatch indicator `Φ(s) = if s false == s true then 0 else 1`. -/
def mismatchPotential (s : Bool → Bool) : ℝ :=
  if s false == s true then 0 else 1

/-- Positive player weights `w false = 1`, `w true = 2`. -/
def playerWeights : Bool → ℝ
  | false => 1
  | true => 2

theorem playerWeights_pos (b : Bool) : 0 < playerWeights b := by
  cases b <;> norm_num [playerWeights]

theorem weightedOnlyGame_isWeightedPotential :
    weightedOnlyGame.IsWeightedPotential playerWeights mismatchPotential := by
  intro s i a
  have hs_eq : ∃ x y : Bool, s = fun b => cond b y x :=
    ⟨s false, s true, by funext b; cases b <;> rfl⟩
  obtain ⟨x, y, rfl⟩ := hs_eq
  cases i <;> cases a <;> cases x <;> cases y <;>
    norm_num [weightedOnlyGame, mismatchPotential, playerWeights, update]

example : weightedOnlyGame.HasFIP :=
  weightedOnlyGame_isWeightedPotential.hasFIP playerWeights_pos

example : ∃ s, weightedOnlyGame.IsPureNash s :=
  weightedOnlyGame_isWeightedPotential.exists_isPureNash playerWeights_pos

example : ∃ Ψ, weightedOnlyGame.mixedExtension.IsWeightedPotential playerWeights Ψ :=
  CostGame.exists_isWeightedPotential_mixedExtension_iff.2
    ⟨mismatchPotential, weightedOnlyGame_isWeightedPotential⟩

example :
    weightedOnlyGame.mixedExtension.IsWeightedPotential playerWeights
      (fun p => CostGame.mixedPotential mismatchPotential (fun j => (p j).1)) :=
  weightedOnlyGame_isWeightedPotential.mixedExtension

example {Ψ : (Bool → Bool) → ℝ}
    (hΨ : weightedOnlyGame.IsWeightedPotential playerWeights Ψ) (s t : Bool → Bool) :
    mismatchPotential s - Ψ s = mismatchPotential t - Ψ t :=
  weightedOnlyGame_isWeightedPotential.sub_eq_sub
    (fun b => (playerWeights_pos b).ne') hΨ s t

/-- Despite having a `(1, 2)`-weighted potential, `weightedOnlyGame` violates `FourCycleZero` and
therefore admits **no** exact potential (nor does its mixed extension, by Lemma 2.10). -/
theorem weightedOnlyGame_not_exactPotential : ¬ ∃ Φ, weightedOnlyGame.IsExactPotential Φ := by
  rw [CostGame.exists_isExactPotential_iff_fourCycleZero]
  intro h4
  have hrect := h4 (show false ≠ true by decide) (fun _ => false) false true false true
  dsimp only at hrect
  norm_num [weightedOnlyGame, update] at hrect

example : ¬ ∃ Ψ, weightedOnlyGame.mixedExtension.IsExactPotential Ψ := by
  rw [CostGame.exists_isExactPotential_mixedExtension_iff]
  exact weightedOnlyGame_not_exactPotential

/-! ### 2. Monderer–Shapley `G₁` counterexample (p. 129): `HasFIP` without ordinal potential -/

/-- The game `G₁ = [[(1, 0), (2, 0)], [(2, 0), (0, 1)]]` of [MondererShapley1996], p. 129, negated
into cost-minimization form:
* `(false, false) ↦ (-1, 0)`
* `(false, true)  ↦ (-2, 0)`
* `(true,  false) ↦ (-2, 0)`
* `(true,  true)  ↦ (0, -1)`. -/
def msCounterexampleG1 : CostGame Bool (fun _ => Bool) where
  cost
    | false => fun s =>
        match s false, s true with
        | false, false => -1
        | false, true => -2
        | true, false => -2
        | true, true => 0
    | true => fun s =>
        match s false, s true with
        | true, true => -1
        | _, _ => 0

/-- Explicit generalized ordinal potential `3, 2, 1, 0` along the unique maximal improvement chain
`(false, false) → (true, false) → (true, true) → (false, true)`. -/
def msCounterexampleG1GenPot (s : Bool → Bool) : ℝ :=
  match s false, s true with
  | false, false => 3
  | true, false => 2
  | true, true => 1
  | false, true => 0

theorem msCounterexampleG1_isGeneralizedOrdinalPotential :
    msCounterexampleG1.IsGeneralizedOrdinalPotential msCounterexampleG1GenPot := by
  intro s i a
  have hs_eq : ∃ x y : Bool, s = fun b => cond b y x :=
    ⟨s false, s true, by funext b; cases b <;> rfl⟩
  obtain ⟨x, y, rfl⟩ := hs_eq
  cases i <;> cases a <;> cases x <;> cases y <;>
    norm_num [msCounterexampleG1, msCounterexampleG1GenPot, update]

theorem msCounterexampleG1_hasFIP : msCounterexampleG1.HasFIP :=
  msCounterexampleG1_isGeneralizedOrdinalPotential.hasFIP

/-- [MondererShapley1996], p. 129: `msCounterexampleG1` has the FIP, yet admits **no** ordinal
potential (`P(a, d) = P(a, c) > P(b, c) > P(b, d) > P(a, d)` in cost order), showing that the
tie-freeness hypothesis of Corollary 2.6 (`exists_isOrdinalPotential_of_hasFIP`) cannot be
dropped. -/
theorem msCounterexampleG1_not_ordinalPotential :
    ¬ ∃ P, msCounterexampleG1.IsOrdinalPotential P := by
  rintro ⟨P, hP⟩
  let ac : Bool → Bool := fun b => cond b false false
  let ad : Bool → Bool := fun b => cond b true false
  let bc : Bool → Bool := fun b => cond b false true
  let bd : Bool → Bool := fun b => cond b true true
  have h_upd_bc : update ac false true = bc := by funext b; cases b <;> rfl
  have h_upd_bd : update bc true true = bd := by funext b; cases b <;> rfl
  have h_upd_ad : update bd false false = ad := by funext b; cases b <;> rfl
  have h_upd_ac_ad : update ac true true = ad := by funext b; cases b <;> rfl
  have h_upd_ad_ac : update ad true false = ac := by funext b; cases b <;> rfl
  have h1 : P bc < P ac := by
    have := (hP ac false true).1 (by norm_num [msCounterexampleG1, ac, update])
    rwa [h_upd_bc] at this
  have h2 : P bd < P bc := by
    have := (hP bc true true).1 (by norm_num [msCounterexampleG1, bc, update])
    rwa [h_upd_bd] at this
  have h3 : P ad < P bd := by
    have := (hP bd false false).1 (by norm_num [msCounterexampleG1, bd, update])
    rwa [h_upd_ad] at this
  have h4 : ¬ P ad < P ac := by
    intro hlt
    have := (hP ac true true).2 (by rwa [h_upd_ac_ad])
    norm_num [msCounterexampleG1, ac, update] at this
  have h5 : ¬ P ac < P ad := by
    intro hlt
    have := (hP ad true false).2 (by rwa [h_upd_ad_ac])
    norm_num [msCounterexampleG1, ad, update] at this
  linarith

/-- Perturbing the single tie in `msCounterexampleG1` restores Corollary 2.6
(`exists_isOrdinalPotential_of_hasFIP`), yielding an ordinal potential. -/
noncomputable def tieBrokenG1 : CostGame Bool (fun _ => Bool) where
  cost
    | false => msCounterexampleG1.cost false
    | true => fun s =>
        match s false, s true with
        | true, true => -1
        | false, true => -1 / 2
        | _, _ => 0

theorem tieBrokenG1_hasFIP : tieBrokenG1.HasFIP := by
  have hgen : tieBrokenG1.IsGeneralizedOrdinalPotential msCounterexampleG1GenPot := by
    intro s i a
    have hs_eq : ∃ x y : Bool, s = fun b => cond b y x :=
      ⟨s false, s true, by funext b; cases b <;> rfl⟩
    obtain ⟨x, y, rfl⟩ := hs_eq
    cases i <;> cases a <;> cases x <;> cases y <;>
      norm_num [tieBrokenG1, msCounterexampleG1, msCounterexampleG1GenPot, update]
  exact hgen.hasFIP

example : ∃ Φ, tieBrokenG1.IsOrdinalPotential Φ := by
  refine tieBrokenG1.exists_isOrdinalPotential_of_hasFIP tieBrokenG1_hasFIP ?_
  intro i s a b hab
  have hs_eq : ∃ x y : Bool, s = fun c => cond c y x :=
    ⟨s false, s true, by funext c; cases c <;> rfl⟩
  obtain ⟨x, y, rfl⟩ := hs_eq
  cases a <;> cases b <;> simp at hab <;> cases i <;> cases x <;> cases y <;>
    norm_num [tieBrokenG1, msCounterexampleG1, update]

/-! ### 3. Theorem 2.8 & Corollary 2.9: Matching Pennies curl vs. Prisoner's Dilemma sweep -/

/-- Matching Pennies in cost form: player `false` wants match (`±1`), player `true` wants mismatch
(`∓1`). -/
def matchingPenniesCost : CostGame Bool (fun _ => Bool) where
  cost
    | false => fun s => if s false == s true then -1 else 1
    | true => fun s => if s false == s true then 1 else -1

/-- The four pure profiles `(false, false), (true, false), (true, true), (false, true)`. -/
def mpA : Bool → Bool := fun b => cond b false false
/-- Profile `(true, false)`. -/
def mpB : Bool → Bool := fun b => cond b false true
/-- Profile `(true, true)`. -/
def mpC : Bool → Bool := fun b => cond b true true
/-- Profile `(false, true)`. -/
def mpD : Bool → Bool := fun b => cond b true false

/-- Simple closed unilateral path `mpA → mpB → mpC → mpD → mpA` of length `4`. -/
def matchingPenniesFourCycle : CostGame.UnilateralPath Bool (fun _ => Bool) where
  start := mpA
  steps := [⟨false, mpB⟩, ⟨true, mpC⟩, ⟨false, mpD⟩, ⟨true, mpA⟩]
  valid := by
    refine ⟨⟨?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, by decide⟩, trivial⟩ <;>
      (funext b; cases b <;> rfl)

theorem matchingPenniesFourCycle_isSimpleClosed : matchingPenniesFourCycle.IsSimpleClosed := by
  refine ⟨rfl, ?_⟩
  simp only [matchingPenniesFourCycle, CostGame.UnilateralPath.initialVertices,
    CostGame.stepInitialVertices, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, not_false_eq_true, List.nodup_nil, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    (intro h; have hf := congrFun h false; have ht := congrFun h true;
      simp [mpA, mpB, mpC, mpD] at hf ht)

theorem matchingPennies_pathIntegral_eq_eight :
    matchingPenniesCost.pathIntegral matchingPenniesFourCycle = 8 := by
  norm_num [matchingPenniesFourCycle, CostGame.pathIntegral, CostGame.stepIntegral,
    matchingPenniesCost, mpA, mpB, mpC, mpD]

theorem matchingPennies_not_exactPotential : ¬ ∃ Φ, matchingPenniesCost.IsExactPotential Φ := by
  rw [CostGame.exists_isExactPotential_iff_simpleClosedPath_four]
  intro h4
  have h0 := h4 matchingPenniesFourCycle matchingPenniesFourCycle_isSimpleClosed rfl
  rw [matchingPennies_pathIntegral_eq_eight] at h0
  norm_num at h0

/-- Prisoner's Dilemma of [MondererShapley1996], p. 128, in cost form (`G = [[(1,1),(9,0)],
[(0,9),(6,6)]]` negated). -/
def prisonersDilemmaMS : CostGame Bool (fun _ => Bool) where
  cost
    | false => fun s =>
        match s false, s true with
        | false, false => -1
        | false, true => -9
        | true, false => 0
        | true, true => -6
    | true => fun s =>
        match s false, s true with
        | false, false => -1
        | false, true => 0
        | true, false => -9
        | true, true => -6

theorem prisonersDilemmaMS_fourCycleZero : prisonersDilemmaMS.FourCycleZero := by
  intro i j hij s xᵢ yᵢ xⱼ yⱼ
  have hs_eq : ∃ x y : Bool, s = fun b => cond b y x :=
    ⟨s false, s true, by funext b; cases b <;> rfl⟩
  obtain ⟨x, y, rfl⟩ := hs_eq
  cases i <;> cases j <;> simp at hij <;>
    cases xᵢ <;> cases yᵢ <;> cases xⱼ <;> cases yⱼ <;> cases x <;> cases y <;>
    dsimp only <;> norm_num [prisonersDilemmaMS, update]

example : prisonersDilemmaMS.IsExactPotential (prisonersDilemmaMS.potentialOfBase mpC) :=
  prisonersDilemmaMS_fourCycleZero.isExactPotential_potentialOfBase mpC

example : prisonersDilemmaMS.potentialOfBase mpC mpC = 0 :=
  prisonersDilemmaMS.potentialOfBase_self mpC

example (γ : CostGame.UnilateralPath Bool (fun _ => Bool)) (hγ : γ.IsClosed) :
    prisonersDilemmaMS.pathIntegral γ = 0 :=
  (CostGame.exists_isExactPotential_iff_closedPath.1
    ⟨_, prisonersDilemmaMS_fourCycleZero.isExactPotential_potentialOfBase mpC⟩) γ hγ

example : ¬ ∀ γ : CostGame.UnilateralPath Bool (fun _ => Bool),
    γ.IsSimpleClosed → matchingPenniesCost.pathIntegral γ = 0 := by
  rw [← CostGame.exists_isExactPotential_iff_simpleClosedPath]
  exact matchingPennies_not_exactPotential

example :
    ∃ C D : CostGame Bool (fun _ => Bool),
      C.IsCoordination ∧ D.IsDummy ∧
        ∀ i s, prisonersDilemmaMS.cost i s = C.cost i s + D.cost i s :=
  prisonersDilemmaMS.exists_isExactPotential_iff_coordination_add_dummy.1
    (CostGame.exists_isExactPotential_iff_fourCycleZero.2 prisonersDilemmaMS_fourCycleZero)

/-! ### 4. Three-player polymatrix games: symmetric `PoS = 1`, separable skew, and non-potential -/

/-- Three-player symmetric polymatrix coordination game on `Fin 3`: players `0` and `1` pay `0`
when matching and `2` when mismatching; player `2` pays `0` when matching `1` and `4` when
mismatching `1` (and `0` with `0`). -/
def symPolymatrix3 : PolymatrixGame (Fin 3) (fun _ => Bool) where
  edgeCost i j a b :=
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
      if a == b then 0 else 2
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then
      if a == b then 0 else 4
    else 0

theorem symPolymatrix3_isSymmetric : symPolymatrix3.IsSymmetric := by
  intro i j _ a b
  fin_cases i <;> fin_cases j <;> cases a <;> cases b <;> simp [symPolymatrix3]

example : symPolymatrix3.toCostGame.IsExactPotential symPolymatrix3.edgePotential :=
  symPolymatrix3_isSymmetric.isExactPotential_edgePotential

example : symPolymatrix3.toCostGame.HasFIP :=
  symPolymatrix3_isSymmetric.hasFIP

example :
    ∃ s, symPolymatrix3.toCostGame.IsPureNash s ∧
      ∀ s', symPolymatrix3.toCostGame.socialCost s ≤ symPolymatrix3.toCostGame.socialCost s' :=
  symPolymatrix3_isSymmetric.exists_isPureNash_socialCost_le

example {M N : Type} (G : BimatrixGame M N) :
    (PolymatrixGame.ofBimatrixGame G).toCostGame = G.toCostGame :=
  PolymatrixGame.toCostGame_ofBimatrixGame G

/-- Uniform `(1/2, 1/2)` mixed profile on `symPolymatrix3` exercises `deviationCost_toCostGame`,
`expectedCost_toCostGame`, and `isMixedNash_toCostGame_iff`. -/
noncomputable def uniformBinary3 : Fin 3 → Bool → ℝ :=
  fun _ _ => 1 / 2

theorem uniformBinary3_sum_one (k : Fin 3) : ∑ c : Bool, uniformBinary3 k c = 1 := by
  simp only [uniformBinary3, Fintype.sum_bool]
  norm_num

example : symPolymatrix3.toCostGame.deviationCost uniformBinary3 1 true = 3 ∧
    symPolymatrix3.toCostGame.expectedCost uniformBinary3 1 = 3 ∧
    symPolymatrix3.toCostGame.IsMixedNash uniformBinary3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [symPolymatrix3.deviationCost_toCostGame uniformBinary3_sum_one]
    simp only [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : Fin 3)), Fin.sum_univ_three,
      Fintype.sum_bool, uniformBinary3, symPolymatrix3]
    norm_num
  · rw [symPolymatrix3.expectedCost_toCostGame uniformBinary3_sum_one]
    simp only [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : Fin 3)), Fin.sum_univ_three,
      Fintype.sum_bool, uniformBinary3, symPolymatrix3]
    norm_num
  · rw [symPolymatrix3.isMixedNash_toCostGame_iff]
    refine ⟨fun i => isMixedStrategy_iff.2
        ⟨fun b => by norm_num [uniformBinary3], uniformBinary3_sum_one i⟩,
      fun i a' => ?_⟩
    fin_cases i <;> cases a' <;>
      simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_three,
        Fintype.sum_bool, uniformBinary3, symPolymatrix3] <;>
      norm_num

/-- Three-player **asymmetric** polymatrix game obtained by adding a dummy opponent bonus
`+ (if b then 5 else 0)` to edge `(0, 1)`: `¬ IsSymmetric`, yet `IsSeparableSkew` holds, so an
exact potential still exists! -/
def asymSeparablePolymatrix3 : PolymatrixGame (Fin 3) (fun _ => Bool) where
  edgeCost i j a b :=
    symPolymatrix3.edgeCost i j a b +
      if i = 0 ∧ j = 1 then (if b then 5 else 0) else 0

theorem asymSeparablePolymatrix3_not_isSymmetric : ¬ asymSeparablePolymatrix3.IsSymmetric := by
  intro hsym
  have h01 := hsym (show (0 : Fin 3) ≠ 1 by decide) true true
  norm_num [asymSeparablePolymatrix3, symPolymatrix3] at h01

theorem asymSeparablePolymatrix3_hasExactPotential :
    ∃ Φ, asymSeparablePolymatrix3.toCostGame.IsExactPotential Φ := by
  rw [PolymatrixGame.exists_isExactPotential_toCostGame_iff_isSeparableSkew]
  refine ⟨fun i j a => if i = 1 ∧ j = 0 then -(if a then 5 else 0) else 0,
    fun i j b => if i = 0 ∧ j = 1 then (if b then 5 else 0) else 0, ?_⟩
  intro i j hij a b
  fin_cases i <;> fin_cases j <;> simp at hij <;> cases a <;> cases b <;>
    norm_num [PolymatrixGame.skewEdge, asymSeparablePolymatrix3, symPolymatrix3]

/-- Baseline-zero-normalized asymmetric 3-player polymatrix game: on `(0, 1)`, player `0` pays `1`
at `(true, true)` while player `1` pays `0` everywhere; zero at `z = fun _ => false`. By
`isSymmetric_iff_exists_isExactPotential_of_zero_at_base`, it admits **no** exact potential. -/
def zeroNormAsymPolymatrix3 : PolymatrixGame (Fin 3) (fun _ => Bool) where
  edgeCost i j a b :=
    if i = 0 ∧ j = 1 ∧ a = true ∧ b = true then 1 else 0

theorem zeroNormAsymPolymatrix3_not_exactPotential :
    ¬ ∃ Φ, zeroNormAsymPolymatrix3.toCostGame.IsExactPotential Φ := by
  have hiff := zeroNormAsymPolymatrix3.isSymmetric_iff_exists_isExactPotential_of_zero_at_base
    (fun _ => false) (by
      intro i j _
      refine ⟨fun b => ?_, fun a => ?_⟩ <;>
        (fin_cases i <;> fin_cases j <;> simp [zeroNormAsymPolymatrix3]))
  rw [← hiff]
  intro hsym
  have h01 := hsym (show (0 : Fin 3) ≠ 1 by decide) true true
  norm_num [zeroNormAsymPolymatrix3] at h01

end CslibFrontierTests.GameTheory.PotentialPolymatrix
