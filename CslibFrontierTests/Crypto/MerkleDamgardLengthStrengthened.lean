/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.MerkleDamgard.LengthStrengthened
import CslibFrontier.Probability.PMF.Support

/-!
# Tests for length-strengthened Merkle–Damgård and Theorem 8.3

Exercises known-answer digests of `lengthStrengthenedMD` under an input-dependent compression
function (`xorCompress`), a concrete application of
`succProbability_collisionGame_lengthStrengthenedMD_eq` with proved `hlen` and `hbound`, the
suffix collision behind the `n = 4` overflow example, and the resulting `n = 4` separation (`1`
vs `0`) against `lengthStrengthenedWrapper`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MerkleDamgardLengthStrengthened

open Cslib Cslib.Crypto Cslib.Probability
open scoped NNReal

/-- Concrete `2n → n` XOR compression function splitting its `2n`-bit input into two
`k.length`-bit halves. -/
private def xorCompress (k x : List Bool) : List Bool :=
  (padOrTake k.length (x.take k.length)).zipWith Bool.xor
    (padOrTake k.length (x.drop k.length))

private theorem length_xorCompress (k x : List Bool) : (xorCompress k x).length = k.length := by
  simp [xorCompress]

/-- Known-answer digest on the empty message at `n = 4`: one padding block `1001` XORed with
`IV = 0000`. -/
example :
    lengthStrengthenedMD xorCompress [false, false, false, false] [] =
      [true, false, false, true] := by
  decide

/-- Known-answer digest on a 5-bit message at `n = 4`: two blocks `[1011, 0110]` XORed with `IV`. -/
example :
    lengthStrengthenedMD xorCompress [false, false, false, false] [true, false, true, true, false] =
      [true, true, false, true] := by
  decide

private def validFive (_ : ℕ) (m : List Bool) : Bool :=
  decide (m.length = 5)

private noncomputable def fiveBitCollider : CollisionFinder :=
  fun _ _ => pure ([true, false, false, false, false], [false, false, false, false, true])

private theorem forall_length_eq_four {P : List Bool → Prop}
    (h : ∀ a b c d : Bool, P [a, b, c, d]) : ∀ k : List Bool, k.length = 4 → P k := by
  rintro (_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩) hk <;>
    first
    | (simp only [List.length_nil, List.length_cons] at hk; omega)
    | exact h a b c d

private theorem eval_collisionGame_four_eq_pure
    (H : List Bool → List Bool → List Bool) (valid : ℕ → List Bool → Bool)
    (m₁ m₂ : List Bool) (b : Bool)
    (hb : ∀ a c d e : Bool, isCollision H valid 4 [a, c, d, e] m₁ m₂ = b) :
    ProbComp.eval (collisionGame H valid (fun _ _ => pure (m₁, m₂)) 4) = PMF.pure b := by
  unfold collisionGame
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
  refine Cslib.Probability.PMF.bind_eq_pure_of_forall_mem_support fun k hk => ?_
  rw [BitString.eval_sampleList] at hk
  have hklen : k.length = 4 := BitString.length_of_mem_support_uniformList hk
  refine congrArg PMF.pure ?_
  clear hk
  revert k hklen
  exact forall_length_eq_four hb

/-- Concrete application of `succProbability_collisionGame_lengthStrengthenedMD_eq` at `n = 4`
for `xorCompress` and `validFive`: both `hlen` and `hbound` hold, the hash collision game has
success probability `1`, and the wrapper's compression collision game has equal probability `1`. -/
example :
    Game.succProbability
        (ProbComp.eval
          (collisionGame (lengthStrengthenedMD xorCompress) validFive fiveBitCollider 4)) =
      Game.succProbability
        (ProbComp.eval
          (collisionGame xorCompress validCompressionInput
            (lengthStrengthenedWrapper xorCompress validFive fiveBitCollider) 4)) ∧
      Game.succProbability
          (ProbComp.eval
            (collisionGame (lengthStrengthenedMD xorCompress) validFive fiveBitCollider 4)) =
        1 := by
  have hlen : ∀ k x, k.length = 4 → x.length = 2 * 4 → (xorCompress k x).length = 4 :=
    fun k x hk _ => (length_xorCompress k x).trans hk
  have hbound : ∀ m, validFive 4 m = true → mdLengthBlockCount 4 m < 2 ^ (4 / 2) := by
    intro m hm
    unfold validFive at hm
    simp only [decide_eq_true_eq] at hm
    unfold mdLengthBlockCount
    omega
  refine ⟨succProbability_collisionGame_lengthStrengthenedMD_eq xorCompress validFive
    fiveBitCollider 4 hlen hbound, ?_⟩
  have htrue :
      ProbComp.eval
          (collisionGame (lengthStrengthenedMD xorCompress) validFive fiveBitCollider 4) =
        PMF.pure true :=
    eval_collisionGame_four_eq_pure (lengthStrengthenedMD xorCompress) validFive
      [true, false, false, false, false] [false, false, false, false, true] true
      fun a b c d => by cases a <;> cases b <;> cases c <;> cases d <;> decide
  simp only [htrue, Game.succProbability, PMF.pure_apply, ↓reduceIte, ENNReal.toNNReal_one]

private def zeroCompress (k _ : List Bool) : List Bool :=
  List.replicate k.length false

private noncomputable def overflowAdversary : CollisionFinder :=
  fun _ _ => pure ([false, false], List.replicate 26 false)

/-- At `n = 4` (`2 ^ (4 / 2) = 4`), `List.replicate 26 false` overflows the `2`-bit block-count
field and its padded blocks have `mdLengthBlocks 4 [false, false]` as a suffix. -/
example :
    mdLengthBlocks 4 [false, false] <:+ mdLengthBlocks 4 (List.replicate 26 false) := by
  decide

/-- Under `zeroCompress` at `n = 4` with all bit strings valid, `[false, false]` and
`List.replicate 26 false` collide in `lengthStrengthenedMD` (`1`), while their padded block lists
share the same suffix blocks so `lengthStrengthenedWrapper` finds no collision (`0`). -/
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
  constructor
  · have htrue :
        ProbComp.eval
            (collisionGame (lengthStrengthenedMD zeroCompress) (fun _ _ => true)
              overflowAdversary 4) =
          PMF.pure true :=
      eval_collisionGame_four_eq_pure (lengthStrengthenedMD zeroCompress) (fun _ _ => true)
        [false, false] (List.replicate 26 false) true
        fun a b c d => by cases a <;> cases b <;> cases c <;> cases d <;> decide
    simp only [htrue, Game.succProbability, PMF.pure_apply, ↓reduceIte, ENNReal.toNNReal_one]
  · have hfalse :
        ProbComp.eval
            (collisionGame zeroCompress validCompressionInput
              (lengthStrengthenedWrapper zeroCompress (fun _ _ => true) overflowAdversary) 4) =
          PMF.pure false := by
      unfold collisionGame lengthStrengthenedWrapper overflowAdversary
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
      refine Cslib.Probability.PMF.bind_eq_pure_of_forall_mem_support fun k hk => ?_
      rw [BitString.eval_sampleList] at hk
      have hklen : k.length = 4 := BitString.length_of_mem_support_uniformList hk
      refine congrArg PMF.pure ?_
      clear hk
      revert k hklen
      refine forall_length_eq_four ?_
      intro a b c d
      cases a <;> cases b <;> cases c <;> cases d <;> decide
    simp only [hfalse, Game.succProbability, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte,
      ENNReal.toNNReal_zero]

end CslibFrontierTests.Crypto.MerkleDamgardLengthStrengthened
