import CslibFrontier.Crypto.Computational.LWE.NormalForm
import CslibFrontier.Crypto.Computational.LPN
import CslibFrontier.Crypto.Computational.LWE.SearchToDecision

namespace CslibFrontierTests.Crypto.LWENormalSearchToDecisionAndLPN

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeLWE

/--
info: 'Cslib.Crypto.PrimeLWE.decisionNormalForm' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms decisionNormalForm

/--
info: 'Cslib.Crypto.PrimeLWE.searchNormalForm' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms searchNormalForm

/--
info: 'Cslib.Crypto.SearchLPN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.SearchLPN

/-- Boundary example for decisionNormalForm: zero dims and zero samples -/
example {noise : PMF (ZMod 2)} (adversary : List Bool → ProbComp Bool) :
    ↑((distinguishingGame (realEnsembleErrorSecret (fun _ => 0) (fun _ => 0) (fun _ => 2)
      (fun _ => noise) 0) adversary).advantage
      (distinguishingGame (uniformEnsemble (fun _ => 0) (fun _ => 0) (fun _ => 2) 0)
      adversary)) ≤
    ↑((distinguishingGame (realEnsemble (fun _ => 0) (fun _ => 0) (fun _ => 2)
      (fun _ => noise) 0) (reduceNormalDecision (n := 0) (m := 0) (q := 2) adversary)).advantage
      (distinguishingGame (uniformEnsemble (fun _ => 0) (fun _ => 0) (fun _ => 2) 0)
      (reduceNormalDecision (n := 0) (m := 0) (q := 2) adversary))) +
    ((PMF.uniformOfFintype (Matrix (Fin 0) (Fin 0) (ZMod 2))).toOuterMeasure
      {A | A.det = 0}).toReal :=
  decisionNormalForm (n := 0) (m := 0) (q := 2) adversary

/-- Boundary example for searchNormalForm: zero dims and zero samples -/
example {noise : PMF (ZMod 2)} (adversary : List Bool → ProbComp (List Bool)) :
    ↑(searchGameErrorSecret 0 0 2 noise adversary).succProbability ≤
    ↑(searchGame 0 0 2 noise
      (reduceNormalSearch (n := 0) (m := 0) (q := 2) adversary)).succProbability +
    ((PMF.uniformOfFintype (Matrix (Fin 0) (Fin 0) (ZMod 2))).toOuterMeasure
      {A | A.det = 0}).toReal :=
  searchNormalForm (n := 0) (m := 0) (q := 2) adversary

/-- LPN boundary -/
example : SearchLPN (fun _ => 0) (fun _ => 0) (fun _ => 0) ↔
  SearchLWE (fun _ => 0) (fun _ => 0) (fun _ => 2) (fun _ => bernoulliZMod2 0) := Iff.rfl

/-- Genuine positive-gap LWE distinguisher testing `b = 0` (`[0 | 0]` or `[0 | 1]`). -/
def posGapDistinguisher (b : List Bool) : ProbComp Bool :=
  pure (decide
    (b = encMatrix 1 2 2 (Matrix.of ![![0, 0]]) ∨
      b = encMatrix 1 2 2 (Matrix.of ![![0, 1]])))

private def mat11Equiv : ZMod 2 ≃ Matrix (Fin 1) (Fin 1) (ZMod 2) where
  toFun a _ _ := a
  invFun A := A 0 0
  left_inv _ := rfl
  right_inv A := by ext i j; fin_cases i; fin_cases j; rfl

private def mat12Equiv : ZMod 2 × ZMod 2 ≃ Matrix (Fin 1) (Fin 2) (ZMod 2) where
  toFun p := Matrix.of fun _ => ![p.1, p.2]
  invFun M := (M 0 0, M 0 1)
  left_inv p := by cases p; rfl
  right_inv M := by ext i j; fin_cases i; fin_cases j <;> rfl

private theorem pi_fin1_pure_zero :
    PMF.pi (fun _ : Fin 1 => PMF.pure (0 : ZMod 2)) = PMF.pure (fun _ => 0) := by
  ext e
  have he : (e = fun _ => 0) ↔ e 0 = 0 :=
    ⟨fun h => congrFun h 0, fun h => funext fun i => by fin_cases i; exact h⟩
  simp [PMF.pi_apply, PMF.pure_apply, he]

private theorem posGapDistinguisher_encMatrix (M : Matrix (Fin 1) (Fin 2) (ZMod 2)) :
    posGapDistinguisher (encMatrix 1 2 2 M) = pure (decide (M 0 0 = 0)) := by
  have hiff : (M = Matrix.of ![![0, 0]] ∨ M = Matrix.of ![![0, 1]]) ↔ M 0 0 = 0 := by
    revert M; decide
  simp only [posGapDistinguisher, EmbeddingLike.apply_eq_iff_eq]
  exact congrArg pure (decide_eq_decide.mpr hiff)

/-- With `noise = pure 0`, error-secret samples have `s = 0` and `e = 0`, so `b = 0` always and
`posGapDistinguisher` has error-secret advantage `|1 - 1 / 2| = 1 / 2`. -/
theorem posGapDistinguisher_errorSecret_advantage :
    (Game.advantage
      (distinguishingGame
        (realEnsembleErrorSecret (fun _ => 1) (fun _ => 1) (fun _ => 2) (fun _ => pure 0) 0)
        posGapDistinguisher)
      (distinguishingGame
        (uniformEnsemble (fun _ => 1) (fun _ => 1) (fun _ => 2) 0)
        posGapDistinguisher) : ℝ) = 1 / 2 := by
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability]
  have hreal :
      (distinguishingGame
        (realEnsembleErrorSecret (fun _ => 1) (fun _ => 1) (fun _ => 2) (fun _ => pure 0) 0)
        posGapDistinguisher true).toReal = 1 := by
    rw [distinguishingGame_eq_bind, realEnsembleErrorSecret, PMF.monad_bind_eq_bind, PMF.bind_map]
    change (((publicMatrixLawErrorSecret 1 1 2 (pure 0)).bind fun M =>
      ProbComp.eval (posGapDistinguisher (encMatrix 1 2 2 M))) true).toReal = 1
    simp only [posGapDistinguisher_encMatrix, ProbComp.eval_pure, publicMatrixLawErrorSecret,
      pi_fin1_pure_zero, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind]
    rw [← PMF.uniformOfFintype_map_equiv mat11Equiv]
    simp only [PMF.bind_map, Function.comp_def, PMF.bind_apply, PMF.uniformOfFintype_apply,
      PMF.pure_apply, LWE.publicMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
      Fin.cons_zero, mat11Equiv, mul_zero, add_zero, decide_true, ↓reduceIte,
      mul_one, tsum_fintype, ZMod.card]
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    simp only [Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
    norm_num [ENNReal.toReal_add]
  have hunif :
      (distinguishingGame
        (uniformEnsemble (fun _ => 1) (fun _ => 1) (fun _ => 2) 0)
        posGapDistinguisher true).toReal = 1 / 2 := by
    rw [distinguishingGame_eq_bind, uniformEnsemble, PMF.monad_bind_eq_bind, PMF.bind_map]
    change (((PMF.uniformOfFintype (Matrix (Fin 1) (Fin 2) (ZMod 2))).bind fun M =>
      ProbComp.eval (posGapDistinguisher (encMatrix 1 2 2 M))) true).toReal = 1 / 2
    simp only [posGapDistinguisher_encMatrix, ProbComp.eval_pure]
    rw [← PMF.uniformOfFintype_map_equiv mat12Equiv, ← PMF.uniformOfFintype_prod]
    simp only [PMF.bind_map, PMF.map_bind, PMF.bind_bind, Function.comp_def, PMF.bind_apply,
      PMF.uniformOfFintype_apply, PMF.pure_apply, mat12Equiv, Equiv.coe_fn_mk, Matrix.of_apply,
      Matrix.cons_val_zero, tsum_fintype, ZMod.card]
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    simp only [Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
    norm_num [ENNReal.toReal_add, ENNReal.toReal_mul]
  rw [hreal, hunif]
  norm_num

example :
    (1 / 2 : ℝ) ≤
    ↑((distinguishingGame (realEnsemble (fun _ => 1) (fun _ => 2) (fun _ => 2)
      (fun _ => pure 0) 0) (reduceNormalDecision (n := 1) (m := 1) (q := 2)
      posGapDistinguisher)).advantage
      (distinguishingGame (uniformEnsemble (fun _ => 1) (fun _ => 2) (fun _ => 2) 0)
      (reduceNormalDecision (n := 1) (m := 1) (q := 2) posGapDistinguisher))) +
    ((PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (ZMod 2))).toOuterMeasure
      {A | A.det = 0}).toReal := by
  have h := decisionNormalForm (n := 1) (m := 1) (q := 2) (noise := pure 0) posGapDistinguisher
  rwa [posGapDistinguisher_errorSecret_advantage] at h

-- Singular top block reduction logic on zero word
example : reduceNormalDecision (n := 1) (m := 0) (q := 2) (fun _ => pure true) [false, false]
    = pure false := by
  have h : Turing.MultiTapeTM.frames [false, false] = [[], []] := by
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]
    rfl
  simp [reduceNormalDecision, topBlock, decodeMatrix, gaussInv?, h]

-- Genuine encoded singular block
example : reduceNormalDecision (n := 1) (m := 0) (q := 2) (fun _ => pure true)
    (encMatrix 1 2 2 ![![0, 0]]) = pure false := by
  change reduceNormalDecision (n := 1) (m := 0) (q := 2) (fun _ => pure true)
    (encMatrix 1 2 2 (Matrix.of ![![0, 0]])) = pure false
  unfold reduceNormalDecision
  rw [decodeMatrix_encMatrix]
  simp [gaussInv?, topBlock]

-- Genuine encoded invertible block
example : reduceNormalDecision (n := 1) (m := 0) (q := 2) (fun _ => pure true)
    (encMatrix 1 2 2 ![![0, 1]]) = pure true := by
  change reduceNormalDecision (n := 1) (m := 0) (q := 2) (fun _ => pure true)
    (encMatrix 1 2 2 (Matrix.of ![![0, 1]])) = pure true
  unfold reduceNormalDecision
  rw [decodeMatrix_encMatrix]
  simp [gaussInv?, topBlock]

-- Distributional boundary
noncomputable def half_prob : unitInterval := ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩

example : bernoulliZMod2 half_prob = PMF.uniformOfFintype (ZMod 2) := by
  ext x
  fin_cases x
  · change bernoulliZMod2 half_prob 0 = PMF.uniformOfFintype (ZMod 2) 0
    simp [bernoulliZMod2, PMF.uniformOfFintype_apply, PMF.map, PMF.bind_apply,
      PMF.pure_apply, PMF.coin_apply, half_prob]
    norm_num [ENNReal.ofReal_sub, ENNReal.ofReal_div_of_pos]
  · change bernoulliZMod2 half_prob 1 = PMF.uniformOfFintype (ZMod 2) 1
    simp [bernoulliZMod2, PMF.uniformOfFintype_apply, PMF.map, PMF.bind_apply,
      PMF.pure_apply, PMF.coin_apply, half_prob]

end CslibFrontierTests.Crypto.LWENormalSearchToDecisionAndLPN
