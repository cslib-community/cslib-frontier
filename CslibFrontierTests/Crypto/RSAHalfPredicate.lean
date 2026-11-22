/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.RSAHalfPredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.Sampling
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the half predicate of RSA

Clients of Boneh–Shoup Exercise 12.21 on the toy key `N = 3 * 11`, `e = 3`, `d = 7`, which hides
`x = 5` as `y = 26`.
-/

public section

namespace CslibFrontierTests.Crypto.RSAHalfPredicate

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### Part (a) -/

-- The six half-predicate values of `x = 5` modulo `33` (`33 ≤ 2 ^ 6`) recover `x`.
example : lsbRecover 33 6 ((List.range 6).map fun k => decide (33 < 2 * (5 * 2 ^ k % 33))) = 5 :=
  lsbRecover_map_decide_lt_two_mul (by decide) (by decide) (by decide)

-- Oddness is needed: `6 = 2 * 3` is the modulus of an `RSADesc`, and `P_0` and `P_3` agree at
-- every point `r`, so no choice of points recovers `x`.
example : ∀ r < 6, decide (6 < 2 * (0 * r % 6)) = decide (6 < 2 * (3 * r % 6)) := by decide

example : ∃ desc : RSADesc, desc.modulus = 6 :=
  ⟨{ p := 2, q := 3, e := 1, d := 1, hp := by norm_num, hq := by norm_num, hpq := by decide,
     he := by decide, hed := by decide }, rfl⟩

-- `N ≤ 2 ^ m` is needed: for `N = 7` and `m = 2`, the residues `0` and `1` give the same values.
example : (List.range 2).map (fun k => decide (7 < 2 * (0 * 2 ^ k % 7))) =
    (List.range 2).map (fun k => decide (7 < 2 * (1 * 2 ^ k % 7))) := by decide

/-! ### Part (b) -/

/-- The toy RSA parameters `N = 3 * 11`, `e = 3`, `d = 7`. -/
def desc33 : RSADesc :=
  { p := 3, q := 11, e := 3, d := 7, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

-- The inverter asks the half oracle at part (a)'s points: on the key `(33, 3)` and `y = 26`, it
-- calls `H` at `2 ^ (3 * k) * 26 % 33` for `k < Nat.size 33`, ...
example (H : RSAPredictor) (n : ℕ) :
    lsbInverter (halfToLSBPredictor H) n ⟨33, 3⟩ ⟨26, by decide⟩ = (do
      let bits ← (List.range (Nat.size 33)).mapM fun k =>
        H n ⟨33, 3⟩ ⟨2 ^ (k * 3) * 26 % 33, Nat.mod_lt _ (by decide)⟩
      return ⟨lsbRecover 33 (Nat.size 33) bits % 33, Nat.mod_lt _ (by decide)⟩) :=
  lsbInverter_halfToLSBPredictor (by decide) _

-- ... which are the RSA images of `5 * 2 ^ k % 33`, `k = 0, …, 5`.
example : (List.range (Nat.size 33)).map (fun k => 2 ^ (k * 3) * 26 % 33) =
    (List.range 6).map fun k => rsaEval 33 3 (5 * 2 ^ k % 33) := by decide

/-- A half predictor that decrypts with `d = 7`, written with `testBit` (the parity identity) so
that its certificate uses binary arithmetic only. -/
def trapdoorHalfPredictor : RSAPredictor :=
  fun _ _ y => pure ((2 * rsaInvert 33 7 y % 33).testBit 0)

theorem trapdoorHalfPredictor_correct (n : ℕ) (w : Fin desc33.modulus) :
    ProbComp.eval (trapdoorHalfPredictor n desc33.publicKey (desc33.publicKey.eval w)) =
      PMF.pure (decide (desc33.modulus < 2 * w)) := by
  simp only [trapdoorHalfPredictor, ProbComp.eval_pure, RSAPublicKey.val_eval]
  congr 1
  revert w
  decide

theorem isPPT_trapdoorHalfPredictor : trapdoorHalfPredictor.IsPPT := by
  have hinv : ComputableInPolyTime
      (fun x : RSAInput => rsaInvert 33 7 x.challenge) encRSAInput encNat :=
    computableInPolyTime_rsaInvert (ComputableInPolyTime.const 33)
      (ComputableInPolyTime.const 7)
      (RSAInput.computableInPolyTime_challenge_val (by fun_prop))
      (fun _ => by decide)
  have hval : ComputableInPolyTime
      (fun x : RSAInput => 2 * rsaInvert 33 7 x.challenge % 33) encRSAInput encNat :=
    ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hinv)
      (ComputableInPolyTime.const 33)
  have hbit : ComputableInPolyTime
      (fun x : RSAInput => (2 * rsaInvert 33 7 x.challenge % 33).testBit 0) encRSAInput encBool :=
    (ComputableInPolyTime.binary_testBit hval
      (ComputableInPolyTime.const 0))
  exact hbit.isPPTOn

-- On the constant generator of `desc33`, the inverter built from the half oracle wins the RSA
-- inversion experiment with probability `1` (the always-correct hypothesis is satisfiable).
example (n : ℕ) : Game.succProbability
    (rsaInversionGame (fun _ => PMF.pure desc33)
      (lsbInverter (halfToLSBPredictor trapdoorHalfPredictor)) n) = 1 := by
  refine succProbability_rsaInversionGame_halfToLSBPredictor ?_ ?_
  · intro desc hdesc
    rw [PMF.support_pure, Set.mem_singleton_iff] at hdesc
    subst hdesc
    decide
  · intro desc hdesc
    rw [PMF.support_pure, Set.mem_singleton_iff] at hdesc
    subst hdesc
    exact trapdoorHalfPredictor_correct n

-- The certificate of the whole inverter, on a probabilistic half predictor.
example : (lsbInverter (halfToLSBPredictor fun _ _ _ => ProbComp.uniform Bool)).IsPPT :=
  isPPT_lsbInverter (isPPT_halfToLSBPredictor (isPPTOn_uniform_bool encRSAInput))

-- The constant generator of `desc33` is not one-way: the trapdoor half predictor is PPT and
-- always correct, which the corollary rules out under `RSAOneWay`.
example : ¬ RSAOneWay (fun _ => PMF.pure desc33) := by
  intro hRSA
  refine hRSA.not_frequently_alwaysCorrect_halfPredictor
    (Filter.Eventually.of_forall fun _ desc hdesc => ?_) isPPT_trapdoorHalfPredictor ?_
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hdesc
    subst hdesc
    decide
  · exact (Filter.Eventually.of_forall fun n desc hdesc => by
      rw [PMF.support_pure, Set.mem_singleton_iff] at hdesc
      subst hdesc
      exact trapdoorHalfPredictor_correct n).frequently

end CslibFrontierTests.Crypto.RSAHalfPredicate
