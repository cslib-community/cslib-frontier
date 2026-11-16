/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MerkleDamgard.LengthStrengthened
import CslibFrontier.Probability.PMF.Bind

/-!
# Tests for length-strengthened Merkle–Damgård and Theorem 8.3

Exercises the padding length-bound boundary at `n = 4`
(`mdLengthBlockCount 4 (List.replicate 10 false) = 4`), the valid-domain advantage equality of
`succProbability_collisionGame_lengthStrengthenedMD_eq`, and an explicit `n = 4` overflow
collision where `lengthStrengthenedMD` fails suffix-freeness while `lengthStrengthenedWrapper`
fails to extract a compression collision (`1` vs `0`).
-/

-- Test suite consisting only of private helpers and anonymous `example` checks.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MerkleDamgardLengthStrengthened

open Cslib Cslib.Crypto Cslib.Probability
open scoped NNReal

-- Boundary counterexample for `length_mdLengthPad` and `flatten_mdLengthBlocks` at `n = 4`:
-- a ten-zero-bit message has block count `4 = 2 ^ (4 / 2)`, so replacing `<` with `≤` fails.
example :
    mdLengthBlockCount 4 (List.replicate 10 false) = 2 ^ (4 / 2) ∧
      (mdLengthPad 4 (List.replicate 10 false)).length ≠
        mdLengthBlockCount 4 (List.replicate 10 false) * 4 ∧
      (mdLengthBlocks 4 (List.replicate 10 false)).flatten ≠
        mdLengthPad 4 (List.replicate 10 false) := by
  decide

-- Theorem 8.3 advantage equality holds on any domain satisfying
-- `mdLengthBlockCount n m < 2 ^ (n / 2)`.
example (h : List Bool → List Bool → List Bool) (valid : ℕ → List Bool → Bool)
    (adversary : CollisionFinder) (n : ℕ)
    (hlen : ∀ k x, k.length = n → x.length = 2 * n → (h k x).length = n)
    (hbound : ∀ m, valid n m = true → mdLengthBlockCount n m < 2 ^ (n / 2)) :
    Game.succProbability
        (ProbComp.eval (collisionGame (lengthStrengthenedMD h) valid adversary n)) =
      Game.succProbability
        (ProbComp.eval
          (collisionGame h validCompressionInput
            (lengthStrengthenedWrapper h valid adversary) n)) :=
  succProbability_collisionGame_lengthStrengthenedMD_eq h valid adversary n hlen hbound

private def zeroCompress (k _ : List Bool) : List Bool :=
  List.replicate k.length false

private noncomputable def overflowAdversary : CollisionFinder :=
  fun _ _ => pure ([false, false], List.replicate 26 false)

private theorem forall_length_eq_four {P : List Bool → Prop}
    (h : ∀ a b c d : Bool, P [a, b, c, d]) : ∀ k : List Bool, k.length = 4 → P k := by
  rintro (_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩) hk <;>
    first
    | (simp only [List.length_nil, List.length_cons] at hk; omega)
    | exact h a b c d

-- Under `zeroCompress` at `n = 4` with all bit strings valid, `[false, false]` and
-- `List.replicate 26 false` collide in `lengthStrengthenedMD` (`1`), while their padded block lists
-- share the same final two blocks so `lengthStrengthenedWrapper` finds no collision (`0`).
example :
    Game.succProbability
        (ProbComp.eval
          (collisionGame (lengthStrengthenedMD zeroCompress) (fun _ _ => true)
            overflowAdversary 4)) = 1 ∧
      Game.succProbability
        (ProbComp.eval
          (collisionGame zeroCompress validCompressionInput
            (lengthStrengthenedWrapper zeroCompress (fun _ _ => true) overflowAdversary) 4)) =
        0 := by
  have hblocks :
      mdLengthBlocks 4 [false, false] <:+ mdLengthBlocks 4 (List.replicate 26 false) := by
    decide
  constructor
  · have htrue :
        ProbComp.eval
            (collisionGame (lengthStrengthenedMD zeroCompress) (fun _ _ => true)
              overflowAdversary 4) =
          PMF.pure true := by
      unfold collisionGame overflowAdversary
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
      calc
        (ProbComp.eval (BitString.sampleList 4)).bind
            (fun k =>
              PMF.pure
                (isCollision (lengthStrengthenedMD zeroCompress) (fun _ _ => true) 4 k
                  [false, false] (List.replicate 26 false)))
            =
          (ProbComp.eval (BitString.sampleList 4)).bind (fun _ => PMF.pure true) := by
            refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun k hk => ?_
            rw [BitString.eval_sampleList] at hk
            have hklen : k.length = 4 := BitString.length_of_mem_support_uniformList hk
            refine congrArg PMF.pure ?_
            clear hk
            revert k hklen
            refine forall_length_eq_four ?_
            intro a b c d
            cases a <;> cases b <;> cases c <;> cases d <;> decide
        _ = PMF.pure true := by simp only [PMF.bind_const]
    simp only [htrue, Game.succProbability, PMF.pure_apply, ↓reduceIte, ENNReal.toNNReal_one]
  · have hfalse :
        ProbComp.eval
            (collisionGame zeroCompress validCompressionInput
              (lengthStrengthenedWrapper zeroCompress (fun _ _ => true) overflowAdversary) 4) =
          PMF.pure false := by
      unfold collisionGame lengthStrengthenedWrapper overflowAdversary
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
      calc
        (ProbComp.eval (BitString.sampleList 4)).bind _ =
          (ProbComp.eval (BitString.sampleList 4)).bind (fun _ => PMF.pure false) := by
            refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun k hk => ?_
            rw [BitString.eval_sampleList] at hk
            have hklen : k.length = 4 := BitString.length_of_mem_support_uniformList hk
            refine congrArg PMF.pure ?_
            clear hk
            revert k hklen
            refine forall_length_eq_four ?_
            intro a b c d
            cases a <;> cases b <;> cases c <;> cases d <;> decide
        _ = PMF.pure false := by simp only [PMF.bind_const]
    simp only [hfalse, Game.succProbability, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte,
      ENNReal.toNNReal_zero]

end CslibFrontierTests.Crypto.MerkleDamgardLengthStrengthened
