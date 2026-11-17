/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.GenericGroup.DiffieHellman
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# The generic-group bound for CDH: an ordinary client

Uses the public API of `CslibFrontier.Crypto.Computational.GenericGroup.DiffieHellman` through an
ordinary import, with labels in `Fin 128` for a group of order `101`:

* the sharp bound for the adversary that makes no query and outputs its first challenge label:
  success probability at most `8 / 101`;
* both forms of the bound for an adversary that makes one query, the group operation that gives the
  label of `α + β`: at most `23 / 101` and at most `53 / 202`;
* for that adversary, success probability one half is out of reach, since `(3 + 4)² + 4 < 101`;
* primality is needed where the proof uses it: over `ZMod 4`, `X Y = 0` has `8` solutions, more
  than `2 * 4 - 1`; over `ZMod 5`, it has `9 = 2 * 5 - 1`, so the count `2q - 1` is attained.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GenericGroupDiffieHellman

open Cslib Cslib.Crypto.GenericGroup
open scoped NNReal

private instance : Nonempty (ZMod 101 ↪ Fin 128) :=
  Function.Embedding.nonempty_iff_card_le.mpr (by simp [ZMod.card])

/-! ### An adversary without queries -/

/-- Output the first challenge label; no query. -/
private def adv0 (_g u _v : Fin 128) : ProbOracleComp (GroupOracleSpec 101 (Fin 128)) (Fin 128) :=
  pure u

example : (cdhGame adv0).succProbability ≤ 8 / 101 := by
  refine (succProbability_cdhGame_le_choose (T := 0) (by norm_num)
    fun g u v => OracleComp.IsCostBounded.pure _ 0).trans_eq ?_
  norm_num [Nat.choose]

/-! ### An adversary with one query -/

/-- Ask for the label of `α + β`, the group operation on the two challenge labels, and output it;
one query. -/
private def adv1 (g u v : Fin 128) : ProbOracleComp (GroupOracleSpec 101 (Fin 128)) (Fin 128) := do
  let r ← ProbOracleComp.query (spec := GroupOracleSpec 101 (Fin 128)) (.op u v 1 1)
  pure (r.getD g)

private theorem adv1_bounded (g u v : Fin 128) : (adv1 g u v).IsQueryBounded 1 :=
  ((ProbOracleComp.IsQueryBounded.query _).bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono
    (by norm_num)

example : (cdhGame adv1).succProbability ≤ 23 / 101 := by
  refine (succProbability_cdhGame_le_choose (T := 1) (by norm_num) adv1_bounded).trans_eq ?_
  norm_num [Nat.choose]

example : (cdhGame adv1).succProbability ≤ 53 / 202 := by
  refine (succProbability_cdhGame_le (T := 1) (by norm_num) adv1_bounded).trans_eq ?_
  norm_num

/-- With one query in a group of order `101`, success probability one half is out of reach. -/
example : ¬ (1 / 2 ≤ (cdhGame adv1).succProbability) := fun h => by
  have h' := le_of_half_le_succProbability_cdhGame (T := 1) (by norm_num) adv1_bounded h
  norm_num at h'

/-! ### Where primality is used -/

/-- Over `ZMod 4`, which is not a field, `X Y = 0` has `8` solutions, more than `2 * 4 - 1`. -/
example : (Finset.univ.filter fun p : ZMod 4 × ZMod 4 =>
    p.1 * p.2 = 0 * p.1 + 0 * p.2 + 0).card = 8 := by
  decide

/-- Over `ZMod 5`, `X Y = 0` has `2 * 5 - 1 = 9` solutions: the count `2q - 1` is attained. -/
example : (Finset.univ.filter fun p : ZMod 5 × ZMod 5 =>
    p.1 * p.2 = 0 * p.1 + 0 * p.2 + 0).card = 9 := by
  decide

end CslibFrontierTests.Crypto.GenericGroupDiffieHellman
