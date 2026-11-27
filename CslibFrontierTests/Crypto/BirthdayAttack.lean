/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.PRP.BirthdayAttack

/-!
# Tests for `CslibFrontier.Crypto.Primitives.PRP.BirthdayAttack`

Checked positive instances and hypothesis-necessity counterexamples for
`Cslib.Crypto.PRP.birthdayDistinguisher` and
`Cslib.Crypto.PRP.half_le_advantage_birthdayDistinguisher_of_bijective`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.BirthdayAttack

open Cslib Cslib.Crypto
open scoped NNReal

private def boolQueries : Fin 2 → Bool := ![false, true]

private theorem bijective_boolQueries : Function.Bijective boolQueries := by
  decide

private def boolFlipCipher : Bool → Equiv.Perm Bool
  | false => Equiv.refl Bool
  | true => Equiv.swap false true

-- Exact `1/2` advantage and bijective `1/2` lower bound on `Bool`.
example : (PRF.advantage (fun k => ⇑(boolFlipCipher k))
    (PRP.birthdayDistinguisher boolQueries) : ℝ) = 1 / 2 := by
  rw [PRP.coe_advantage_birthdayDistinguisher boolFlipCipher bijective_boolQueries.injective,
    Fintype.card_bool]
  norm_num [Nat.descFactorial]

example : (1 / 2 : ℝ) ≤ PRF.advantage (fun k => ⇑(boolFlipCipher k))
    (PRP.birthdayDistinguisher boolQueries) :=
  PRP.half_le_advantage_birthdayDistinguisher_of_bijective boolFlipCipher bijective_boolQueries
    (by simp)

-- Sub-domain `Q = 3` and full `Q = 4` on `Fin 4` exercise both branches of `min (_ / _) 0.63`.
private def fin4Triple : Fin 3 → Fin 4 := Fin.castLE (by omega)

private theorem injective_fin4Triple : Function.Injective fin4Triple :=
  Fin.castLE_injective (by omega)

example (Key : Type) [Fintype Key] [Nonempty Key] (E : Key → Equiv.Perm (Fin 4)) :
    (3 / 8 : ℝ) ≤ (PRF.advantage (fun k => ⇑(E k))
      (PRP.birthdayDistinguisher fin4Triple) : ℝ) := by
  have h := PRP.min_le_advantage_birthdayDistinguisher E injective_fin4Triple
  rw [Fintype.card_fin] at h
  norm_num at h
  exact h

example (Key : Type) [Fintype Key] [Nonempty Key] (E : Key → Equiv.Perm (Fin 4)) :
    (0.63 : ℝ) ≤ (PRF.advantage (fun k => ⇑(E k))
      (PRP.birthdayDistinguisher (id : Fin 4 → Fin 4)) : ℝ) := by
  have h := PRP.min_le_advantage_birthdayDistinguisher E Function.injective_id
  rw [Fintype.card_fin] at h
  exact le_trans (by norm_num) h

-- Degenerate `Q = 1` gives `0` advantage cleanly.
example (Key : Type) [Fintype Key] [Nonempty Key] (E : Key → Equiv.Perm Bool) :
    (PRF.advantage (fun k => ⇑(E k))
      (PRP.birthdayDistinguisher (fun _ : Fin 1 => false)) : ℝ) = 0 := by
  rw [PRP.coe_advantage_birthdayDistinguisher E (Function.injective_of_subsingleton _),
    Fintype.card_bool]
  norm_num [Nat.descFactorial]

-- Hypothesis necessity: dropping injectivity of `x` lets `PRF.advantage` be `0 < 1/4`.
example : PRF.advantage (fun k => ⇑(boolFlipCipher k))
    (PRP.birthdayDistinguisher (fun _ : Fin 2 => false)) = 0 := by
  have hconst : ∀ f : Bool → Bool,
      decide (¬ Function.Injective (f ∘ (fun _ : Fin 2 => false))) = true := by
    intro f
    refine decide_eq_true fun hinj => ?_
    exact absurd (@hinj 0 1 rfl) (by decide)
  have hreal : ProbComp.eval (PRF.realExperiment (fun k => ⇑(boolFlipCipher k))
      (PRP.birthdayDistinguisher (fun _ : Fin 2 => false))) = PMF.pure true := by
    simp only [PRF.realExperiment, ProbComp.eval_bind, PRP.run_birthdayDistinguisher,
      ProbComp.eval_pure, (fun k => hconst ⇑(boolFlipCipher k)), ProbComp.eval_uniform,
      PMF.bind_const]
  have hideal : ProbComp.eval (PRF.idealExperiment
      (PRP.birthdayDistinguisher (fun _ : Fin 2 => false))) = PMF.pure true := by
    simp only [PRF.idealExperiment, ProbComp.eval_bind, PRP.run_birthdayDistinguisher,
      ProbComp.eval_pure, hconst, ProbComp.eval_uniform, PMF.bind_const]
  rw [PRF.advantage, hreal, hideal, Game.advantage_self]

-- Hypothesis necessity: a non-permutation constant keyed function on `Fin 4` has advantage
-- `3/32 < 1/2`.
example : (PRF.advantage (fun (_ : Unit) (_ : Fin 4) => (0 : Fin 4))
    (PRP.birthdayDistinguisher (id : Fin 4 → Fin 4)) : ℝ) = 3 / 32 := by
  have hcoll : ¬ Function.Injective (fun _ : Fin 4 => (0 : Fin 4)) := fun hinj =>
    absurd (@hinj 0 1 rfl) (by decide)
  have hreal : ProbComp.eval (PRF.realExperiment (fun (_ : Unit) (_ : Fin 4) => (0 : Fin 4))
      (PRP.birthdayDistinguisher (id : Fin 4 → Fin 4))) = PMF.pure true := by
    have htrue : decide (¬ Function.Injective ((fun _ : Fin 4 => (0 : Fin 4)) ∘
        (id : Fin 4 → Fin 4))) = true :=
      decide_eq_true (by simp only [Function.comp_id]; exact hcoll)
    simp only [PRF.realExperiment, ProbComp.eval_bind, PRP.run_birthdayDistinguisher,
      ProbComp.eval_pure, htrue, ProbComp.eval_uniform, PMF.bind_const]
  have hideal : (Game.succProbability (ProbComp.eval (PRF.idealExperiment
      (PRP.birthdayDistinguisher (id : Fin 4 → Fin 4)))) : ℝ) = 29 / 32 := by
    rw [PRP.succProbability_idealExperiment_birthdayDistinguisher Function.injective_id,
      Fintype.card_fin]
    norm_num [Nat.descFactorial]
  rw [PRF.advantage, hreal, Game.coe_advantage_pure_true_left, ← Game.coe_succProbability, hideal]
  norm_num

-- Hypothesis necessity: `2 ≤ Fintype.card D` is required for `1/2 ≤ PRF.advantage`.
example : PRF.advantage (fun (_ : Unit) => ⇑(Equiv.refl Unit))
    (PRP.birthdayDistinguisher (fun _ : Fin 1 => ())) = 0 := by
  rw [← NNReal.coe_inj, PRP.coe_advantage_birthdayDistinguisher _
    (Function.injective_of_subsingleton _), Fintype.card_unit]
  norm_num [Nat.descFactorial]

end CslibFrontierTests.Crypto.BirthdayAttack
