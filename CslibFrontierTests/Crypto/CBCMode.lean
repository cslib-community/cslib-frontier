/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

import CslibFrontier.Crypto.Computational.Encryption.CBCMode
import Mathlib.Data.Nat.Choose.Cast

set_option linter.privateModule false

/-!
# Tests for CBC mode with a random IV

Concrete evaluations and non-vacuity witnesses for
`CslibFrontier/Crypto/Computational/Encryption/CBCMode.lean`. The headline bounds are instantiated
with a concrete adversary whose cost bound is proved, at parameters where they are strictly below
`1`, and the random-permutation bound is compared with (5.22) of [BonehShoup2023].
-/

namespace CslibFrontierTests.Crypto.CBCMode
open Cslib Cslib.Probability Cslib.Crypto

/-- Answering the chain calls with a fixed function `f` gives the CBC ciphertext blocks
`f (c + m₁), f (f (c + m₁) + m₂)`. -/
example (f : BitString 8 → BitString 8) (c m₁ m₂ : BitString 8) :
    (cbcChainQueries c [m₁, m₂]).run (fun y => pure (f y)) =
      pure [f (c + m₁), f (f (c + m₁) + m₂)] :=
  run_cbcChainQueries f c [m₁, m₂]

/-- A two-block left-or-right query. -/
def cbcQueryLR : BlockModeQuery 8 := ([0, 1], [1, 1])

/-- A one-query adversary: it asks `cbcQueryLR` and outputs `true` when the first ciphertext
block is zero. -/
def cbcOneQueryAdversary : BlockModeAdversary 8 := do
  let r ← ProbOracleComp.query (spec := BlockModeSpec 8) cbcQueryLR
  return decide (r.2.head? = some 0)

/-- The adversary asks for two blocks in total, with at most two blocks per query. -/
theorem isCostBounded_cbcOneQueryAdversary :
    OracleComp.IsCostBounded (blockModeCost 2) cbcOneQueryAdversary 2 := by
  unfold cbcOneQueryAdversary ProbOracleComp.query
  exact OracleComp.IsCostBounded.mono
    (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query (Sum.inr cbcQueryLR)) fun _ =>
      OracleComp.IsCostBounded.pure _ 0)
    (by decide)

/-- The PRF reduction for the adversary makes at most two oracle calls. -/
example : ProbOracleComp.IsQueryBounded (cbcReduction 2 true cbcOneQueryAdversary) 2 :=
  isQueryBounded_cbcReduction 2 true isCostBounded_cbcOneQueryAdversary

/-- A one-query adversary asking for one block: it outputs `true` when that ciphertext block is
zero. -/
def cbcOneBlockAdversary : BlockModeAdversary 8 := do
  let r ← ProbOracleComp.query (spec := BlockModeSpec 8) (([0], [1]) : BlockModeQuery 8)
  return decide (r.2.head? = some 0)

/-- The one-block adversary asks for one block in total (`K = 1`). -/
theorem isCostBounded_cbcOneBlockAdversary :
    OracleComp.IsCostBounded (blockModeCost 1) cbcOneBlockAdversary 1 := by
  unfold cbcOneBlockAdversary ProbOracleComp.query
  exact OracleComp.IsCostBounded.mono
    (OracleComp.IsCostBounded.bind
      (OracleComp.IsCostBounded.query (Sum.inr (([0], [1]) : BlockModeQuery 8))) fun _ =>
        OracleComp.IsCostBounded.pure _ 0)
    (by decide)

/-- At `K = 1` both headline bounds are `0`: one query of one block has left-or-right advantage
`0` against CBC mode with a uniform random function and with a uniform random permutation. -/
example :
    (Game.advantage
        (cbcCpaGame (fun f : BitString 8 → BitString 8 => f) 1 false cbcOneBlockAdversary)
        (cbcCpaGame (fun f : BitString 8 → BitString 8 => f) 1 true cbcOneBlockAdversary) :
      ℝ) ≤ 0 ∧
    (Game.advantage
        (cbcCpaGame (fun π : Equiv.Perm (BitString 8) => ⇑π) 1 false cbcOneBlockAdversary)
        (cbcCpaGame (fun π : Equiv.Perm (BitString 8) => ⇑π) 1 true cbcOneBlockAdversary) :
      ℝ) ≤ 0 :=
  ⟨(advantage_cbcCpaGame_randomFunction_le 1 isCostBounded_cbcOneBlockAdversary).trans_eq
      (by norm_num),
    (advantage_cbcCpaGame_randomPermutation_le 1 isCostBounded_cbcOneBlockAdversary).trans_eq
      (by norm_num)⟩

/-- With a uniform random function on 8-bit blocks, the reduction's view is within
`(2 choose 2) / 2 ^ 8 = 1 / 256` of the ideal experiment. -/
example :
    (Game.advantage
        (ProbComp.eval (PRF.idealExperiment (cbcReduction 2 false cbcOneQueryAdversary)))
        (ProbComp.eval (blockModeIdealExperiment 2 cbcOneQueryAdversary)) : ℝ) ≤ 1 / 256 :=
  (advantage_idealExperiment_cbcReduction_le 2 false isCostBounded_cbcOneQueryAdversary).trans_eq
    (by norm_num)

/-- CBC mode with a uniform random function on 8-bit blocks: the adversary's left-or-right
advantage is at most `2 / 2 ^ 8 = 1 / 128`. -/
example :
    (Game.advantage
        (cbcCpaGame (fun f : BitString 8 → BitString 8 => f) 2 false cbcOneQueryAdversary)
        (cbcCpaGame (fun f : BitString 8 → BitString 8 => f) 2 true cbcOneQueryAdversary) :
      ℝ) ≤ 1 / 128 :=
  (advantage_cbcCpaGame_randomFunction_le 2 isCostBounded_cbcOneQueryAdversary).trans_eq
    (by norm_num)

/-- CBC mode with a uniform random permutation of 8-bit blocks: the adversary's left-or-right
advantage is at most `4 / 2 ^ 8 = 1 / 64`, below (5.22)'s `2 Q² ℓ² / N = 8 / 2 ^ 8` for `Q = 1`
query of `ℓ = 2` blocks. -/
example :
    (Game.advantage
        (cbcCpaGame (fun π : Equiv.Perm (BitString 8) => ⇑π) 2 false cbcOneQueryAdversary)
        (cbcCpaGame (fun π : Equiv.Perm (BitString 8) => ⇑π) 2 true cbcOneQueryAdversary) :
      ℝ) ≤ 1 / 64 :=
  (advantage_cbcCpaGame_randomPermutation_le 2 isCostBounded_cbcOneQueryAdversary).trans_eq
    (by norm_num)

/-- The random-permutation bound in the book's form: for `Q` queries of at most `ℓ` blocks,
`K ≤ Q ℓ` and `4 K.choose 2 / 2 ^ n ≤ 2 Q² ℓ² / 2 ^ n`, the first term of (5.22) of
[BonehShoup2023]. -/
example {n K Q ℓ : ℕ} (hK : K ≤ Q * ℓ) :
    4 * ((K.choose 2 : ℝ) / 2 ^ n) ≤ 2 * (Q : ℝ) ^ 2 * ℓ ^ 2 / 2 ^ n := by
  have hKQ : (K : ℝ) ≤ Q * ℓ := by exact_mod_cast hK
  have hK0 : (0 : ℝ) ≤ K := by positivity
  rw [Nat.cast_choose_two, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

/-- The query convention: messages of different lengths, or longer than `ℓ` blocks, encrypt the
empty message and cost nothing. -/
example : blockModeSelect 2 true (([0], [1, 1]) : BlockModeQuery 8) = [] ∧
    blockModeBlocks 1 cbcQueryLR = 0 := by
  decide

end CslibFrontierTests.Crypto.CBCMode
