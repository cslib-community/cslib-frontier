import CslibFrontier.Crypto.Computational.LWE.SearchToDecision

/-! Tests for `CslibFrontier.Crypto.Computational.LWE.SearchToDecision`. -/

namespace CslibFrontierTests.Crypto.LWESearchToDecision

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeLWE

/-- Two estimators per coordinate plus the uniform one, two trials each, one row per block. -/
example : searchSamples 1 2 2 1 = 6 := rfl

example : trueCount ![true, false, true] = 2 := by decide

/-- Re-randomizing `[b | a] = [1 | 2]` over `ZMod 3` by `s' = 1` gives `[1 + 2 | 2] = [0 | 2]`. -/
example :
    rerandomizeSecret (n := 1) (m := 1) (q := 3) (fun _ => ![1, 2]) (fun _ => 1) =
      fun _ => ![0, 2] := by
  funext i c
  fin_cases i
  fin_cases c <;> decide

/-- Trials where the correct guess `0` always accepts and every other estimator never does. -/
def perfectTrials (o : Option (Fin 1 × ZMod 2)) (_ : Fin 4) : Bool :=
  if o = some (0, 0) then true else false

/-- With real acceptance `1` and uniform acceptance `0`, exact counts recover the secret. -/
example : guessSecret perfectTrials = fun _ => 0 := by
  have hcount (o : Option (Fin 1 × ZMod 2)) :
      trueCount (perfectTrials o) = if o = some (0, 0) then 4 else 0 := by
    by_cases h : o = some (0, 0) <;> simp [perfectTrials, trueCount, h]
  refine guessSecret_eq_of_close perfectTrials _ (pR := 1) (pU := 0) ?_ ?_
  · rw [hcount]
    norm_num
  · intro j g
    rw [hcount]
    obtain rfl : j = 0 := Subsingleton.elim _ _
    by_cases hg : g = 0
    · subst hg
      norm_num
    · have hg' : (0, g) ≠ ((0 : Fin 1), (0 : ZMod 2)) := fun h => hg (Prod.ext_iff.mp h).2
      simp only [Option.some.injEq, hg', hg, ite_false]
      norm_num

/-- The concrete reduction specializes to any adversary and repetition count. -/
example (adversary : List Bool → ProbComp Bool) (N : ℕ) :
    1 - (1 * 2 + 1) * (2 * Real.exp (-(N * (Game.advantage
        (distinguishingGame (realEnsemble (fun _ => 1) (fun _ => 3) (fun _ => 2)
          (fun _ => PMF.uniformOfFintype (ZMod 2)) 0) adversary)
        (distinguishingGame (uniformEnsemble (fun _ => 1) (fun _ => 3) (fun _ => 2) 0)
          adversary) : ℝ) ^ 2) / 8)) ≤
      Game.succProbability (searchGame 1 (searchSamples 1 2 N 3) 2
        (PMF.uniformOfFintype (ZMod 2))
        (reduceSearchToDecision (n := 1) (m := 3) (q := 2) N adversary)) := by
  exact_mod_cast searchToDecision adversary N

/--
info: 'Cslib.Crypto.PrimeLWE.searchToDecision' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms searchToDecision

/--
info: 'Cslib.Crypto.PrimeLWE.pi_estimatorLaw_guessSecret_ne_le' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pi_estimatorLaw_guessSecret_ne_le

/-- A positive-gap LWE distinguisher testing whether the target entry `b` is `0`
(`bits = encMatrix 1 2 2 ![![0, 0]]` or `bits = encMatrix 1 2 2 ![![0, 1]]`). -/
def posGapDistinguisher (bits : List Bool) : ProbComp Bool :=
  pure (decide
    (bits = encMatrix 1 2 2 (Matrix.of ![![0, 0]]) ∨
      bits = encMatrix 1 2 2 (Matrix.of ![![0, 1]])))

private def vec1Equiv : ZMod 2 ≃ (Fin 1 → ZMod 2) where
  toFun x _ := x
  invFun v := v 0
  left_inv _ := rfl
  right_inv v := funext fun i => by fin_cases i; rfl

private def mat11Equiv : ZMod 2 ≃ Matrix (Fin 1) (Fin 1) (ZMod 2) where
  toFun a := Matrix.of fun _ _ => a
  invFun A := A 0 0
  left_inv _ := rfl
  right_inv A := by ext i j; fin_cases i; fin_cases j; rfl

private theorem mat11Equiv_apply (a : ZMod 2) (i j : Fin 1) : mat11Equiv a i j = a := rfl

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

/-- Under `n = m = 1, q = 2` and zero noise, `posGapDistinguisher` accepts real samples with
probability `3 / 4` (since `a * s = 0` for `3` of the `4` uniform pairs `(s, a)`). -/
theorem posGapDistinguisher_real_accept :
    (Game.succProbability (distinguishingGame
      (realEnsemble (fun _ => 1) (fun _ => 1) (fun _ => 2) (fun _ => pure 0) 0)
      posGapDistinguisher) : ℝ) = 3 / 4 := by
  rw [Game.coe_succProbability, distinguishingGame_eq_bind, realEnsemble, PMF.monad_bind_eq_bind,
    PMF.bind_map]
  change (((LWE.publicMatrixLaw 1 1 (pure (0 : ZMod 2))).bind fun M =>
    ProbComp.eval (posGapDistinguisher (encMatrix 1 2 2 M))) true).toReal = 3 / 4
  simp only [posGapDistinguisher_encMatrix, ProbComp.eval_pure, LWE.publicMatrixLaw,
    pi_fin1_pure_zero, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind]
  rw [← PMF.uniformOfFintype_map_equiv vec1Equiv, ← PMF.uniformOfFintype_map_equiv mat11Equiv]
  simp only [PMF.bind_map, Function.comp_def, PMF.bind_apply, PMF.uniformOfFintype_apply,
    PMF.pure_apply, LWE.publicMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.cons_zero,
    vec1Equiv, mat11Equiv_apply, Equiv.coe_fn_mk, add_zero, tsum_fintype, ZMod.card]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
  simp only [Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), mul_zero, zero_mul, mul_one,
    decide_true, (by decide : decide ((1 : ZMod 2) = 0) = false), Bool.true_eq_false, ↓reduceIte,
    add_zero, Nat.cast_ofNat, ENNReal.inv_two_add_inv_two]
  rw [ENNReal.toReal_add (by norm_num) (ENNReal.mul_ne_top (by norm_num) (by norm_num)),
    ENNReal.toReal_mul]
  norm_num

/-- Under `n = m = 1, q = 2`, `posGapDistinguisher` accepts uniform samples with probability
`1 / 2`. -/
theorem posGapDistinguisher_uniform_accept :
    (Game.succProbability (distinguishingGame
      (uniformEnsemble (fun _ => 1) (fun _ => 1) (fun _ => 2) 0)
      posGapDistinguisher) : ℝ) = 1 / 2 := by
  rw [Game.coe_succProbability, distinguishingGame_eq_bind, uniformEnsemble, PMF.monad_bind_eq_bind,
    PMF.bind_map]
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

/-- `posGapDistinguisher` achieves Decision LWE advantage `|3 / 4 - 1 / 2| = 1 / 4`. -/
theorem posGapDistinguisher_advantage :
    (Game.advantage
      (distinguishingGame
        (realEnsemble (fun _ => 1) (fun _ => 1) (fun _ => 2) (fun _ => pure 0) 0)
        posGapDistinguisher)
      (distinguishingGame
        (uniformEnsemble (fun _ => 1) (fun _ => 1) (fun _ => 2) 0)
        posGapDistinguisher) : ℝ) = 1 / 4 := by
  rw [Game.coe_advantage, posGapDistinguisher_real_accept, posGapDistinguisher_uniform_accept]
  norm_num

/-- Concrete `searchToDecision` lower bound rewritten with `posGapDistinguisher`'s `1 / 4`
distinguishing advantage. -/
theorem searchToDecision_posGapDistinguisher (N : ℕ) :
    1 - (1 * 2 + 1) * (2 * Real.exp (-(N * (1 / 4 : ℝ) ^ 2) / 8)) ≤
      Game.succProbability (searchGame 1 (searchSamples 1 2 N 1) 2
        (pure 0)
        (reduceSearchToDecision (n := 1) (m := 1) (q := 2) N posGapDistinguisher)) := by
  have h := searchToDecision (n := 1) (m := 1) (q := 2) (noise := pure 0) posGapDistinguisher N
  rwa [posGapDistinguisher_advantage] at h

end CslibFrontierTests.Crypto.LWESearchToDecision
