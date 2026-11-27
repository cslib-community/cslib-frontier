/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SecondPreimageResistant.XorTarget
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for `xorTargetHash` and Theorem 8.12

Checks for `CslibFrontier/Crypto/Computational/SecondPreimageResistant/XorTarget.lean` as a
`module` client with ordinary imports:

* Concrete evaluation of `validFixedLengthInput` and `xorTargetHash`.
* Unconditional instantiation of Theorem 8.12 from Definition 8.6's fixed-length `{0, 1}ⁿ`
  second-preimage resistance with `H = id` (`targetCollisionResistantOn_xorTargetHash_id`).
* Necessity of the `validFixedLengthInput` restriction (`decide (m.length = n)`): without it, the
  two-stage strict PPT adversary `paddingCollisionAdversary` (choosing `m₀ = []` and returning
  `m₁ = [false]`) wins `targetCollisionGame` with probability `1` at every parameter `n` for every
  `H`, refuting unrestricted `TargetCollisionResistant id (xorTargetHash H)`
  (`not_targetCollisionResistant_xorTargetHash`).
* Necessity of `hvalid` in Theorem 8.12: `SecondPreimageResistantOn (fun _ => []) (fun _ _ =>
  false)` holds vacuously, while `sameLengthCollisionAdversary` (choosing `replicate n false` and
  returning `replicate n true`) wins `targetCollisionGame` against `xorTargetHash (fun _ => [])`
  on `validFixedLengthInput` with probability `1` for every `n ≥ 1`, refuting both the concrete
  reduction at `n = 1` and the asymptotic theorem when `hvalid` fails.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.XorTargetHash

open Cslib Cslib.Crypto Cslib.ProbComp Cslib.Probability
open Turing.MultiTapeTM
open scoped NNReal ENNReal

example : validFixedLengthInput 2 [true, false] = true := rfl

example : validFixedLengthInput 2 [true] = false := rfl

example : xorTargetHash id 2 [true, false] [true, true] = [false, true] := rfl

/-- The identity on bit strings satisfies Definition 8.6 (`SecondPreimageResistantOn` on
`{0, 1}ⁿ`). -/
theorem secondPreimageResistantOn_id :
    SecondPreimageResistantOn id (fun n w => decide (w.length = n)) :=
  SecondPreimageResistantOn.of_injective (ComputableInPolyTime.id' (encIn := encBits))
    fun _ _ _ _ _ h => h

/-- Theorem 8.12 instantiated with `H = id` on `{0, 1}ⁿ`: `xorTargetHash id` is unconditionally
target collision-resistant on `n`-bit messages. -/
theorem targetCollisionResistantOn_xorTargetHash_id :
    TargetCollisionResistantOn id (xorTargetHash id) validFixedLengthInput :=
  secondPreimageResistantOn_id.targetCollisionResistantOn_xorTargetHash
    (Filter.Eventually.of_forall fun _ _ hw => decide_eq_true hw)

/-- Two-stage adversary that outputs `m₀ = []` and `m₁ = [false]`. Without
`validFixedLengthInput`, `BitString.listXor n [k, []] = BitString.listXor n [k, [false]]` for every
`n` and `k`, so this adversary breaks `xorTargetHash H` with probability `1` for every `H`
(including `H = id`), showing that `validFixedLengthInput` cannot be omitted in Theorem 8.12. -/
def paddingCollisionAdversary : TargetCollisionFinder where
  choose := fun _ => pure ([], [])
  find := fun _ _ _ => pure [false]

theorem isPPT_paddingCollisionAdversary : paddingCollisionAdversary.IsPPT where
  choose := (ComputableInPolyTime.const ([], [])).isPPTOn
  find := (ComputableInPolyTime.const [false]).isPPTOn

theorem eval_targetCollisionGame_unrestricted_paddingCollisionAdversary
    (H : List Bool → List Bool) (n : ℕ) :
    ProbComp.eval
      (targetCollisionGame id (xorTargetHash H) (fun _ _ => true)
        paddingCollisionAdversary n) = PMF.pure true := by
  have hxor (k : List Bool) :
      BitString.listXor n [k, []] = BitString.listXor n [k, [false]] := by
    have h01 : BitString.ofList n [] = BitString.ofList n [false] := by
      ext ⟨i, hi⟩
      cases i <;> simp [BitString.ofList]
    rw [BitString.listXor_pair, BitString.listXor_pair, h01]
  have hcol (k : List Bool) :
      isCollision (xorTargetHash H n) (fun _ _ => true) n k [] [false] = true := by
    rw [isCollision_eq_true_iff]
    exact ⟨rfl, rfl, by decide, by simp [xorTargetHash, hxor k]⟩
  simp only [targetCollisionGame, paddingCollisionAdversary, id_eq, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind, hcol, PMF.bind_const]

theorem not_targetCollisionResistant_xorTargetHash (H : List Bool → List Bool) :
    ¬ TargetCollisionResistant id (xorTargetHash H) := by
  refine not_targetCollisionResistantOn_of_le_succProbability one_ne_zero
    paddingCollisionAdversary isPPT_paddingCollisionAdversary fun n => ?_
  rw [eval_targetCollisionGame_unrestricted_paddingCollisionAdversary, Game.succProbability,
    PMF.pure_apply_self, ENNReal.toNNReal_one]

/-- Two-stage adversary that chooses `replicate n false` and returns `replicate n true`. Against
`fun _ => []`, both messages have length `n`, collide under `xorTargetHash`, and show `hvalid`
cannot be omitted in Theorem 8.12. -/
def sameLengthCollisionAdversary : TargetCollisionFinder where
  choose := fun n => pure (List.replicate n false, [])
  find := fun n _ _ => pure (List.replicate n true)

theorem isPPT_sameLengthCollisionAdversary : sameLengthCollisionAdversary.IsPPT where
  choose := by
    dsimp [sameLengthCollisionAdversary]
    exact (show ComputableInPolyTime (fun n : ℕ => (List.replicate n false, ([] : List Bool)))
      encUnary (encPair encBits encBits) by polytime).isPPTOn
  find := by
    dsimp [sameLengthCollisionAdversary]
    exact (show ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => List.replicate p.1 true)
      (encPair encUnary (encPair encBits encBits)) encBits by polytime).isPPTOn

theorem eval_targetCollisionGame_const_sameLengthCollisionAdversary
    {n : ℕ} (hn : 1 ≤ n) :
    ProbComp.eval
      (targetCollisionGame id (xorTargetHash (fun _ => [])) validFixedLengthInput
        sameLengthCollisionAdversary n) = PMF.pure true := by
  have hcol (k : List Bool) :
      isCollision (xorTargetHash (fun _ => []) n) validFixedLengthInput n k
        (List.replicate n false) (List.replicate n true) = true := by
    rw [isCollision_eq_true_iff]
    refine ⟨by simp, by simp, ?_, rfl⟩
    cases n with
    | zero => omega
    | succ m => simp [List.replicate_succ]
  simp only [targetCollisionGame, sameLengthCollisionAdversary, id_eq, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind, hcol, PMF.bind_const]

/-- Without `hvalid`, `succProbability_targetCollisionGame_xorTargetHash_le` fails at `n = 1` for
`H := fun _ => []` and `valid := fun _ _ => false` (`1` vs `0`). -/
theorem not_succProbability_le_without_hvalid :
    ¬ Game.succProbability
        (ProbComp.eval
          (targetCollisionGame id (xorTargetHash (fun _ => [])) validFixedLengthInput
            sameLengthCollisionAdversary 1)) ≤
      Game.succProbability
        (ProbComp.eval
          (secondPreimageGameOn (fun _ => []) (fun _ _ => false)
            (xorTargetToSecondPreimage sameLengthCollisionAdversary) 1)) := by
  have hwin :
      Game.succProbability
        (ProbComp.eval
          (targetCollisionGame id (xorTargetHash (fun _ => [])) validFixedLengthInput
            sameLengthCollisionAdversary 1)) = 1 := by
    rw [eval_targetCollisionGame_const_sameLengthCollisionAdversary (le_refl 1),
      Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]
  have hlose :
      ProbComp.eval
        (secondPreimageGameOn (fun _ => []) (fun _ _ => false)
          (xorTargetToSecondPreimage sameLengthCollisionAdversary) 1) = PMF.pure false := by
    unfold secondPreimageGameOn
    simp [ProbComp.eval_bind, show ∀ p : PMF (List Bool),
      PMF.map (fun _ => false) p = PMF.pure false from fun p => p.map_const false]
  rw [hwin, hlose, Game.succProbability, PMF.pure_apply]
  simp

/-- Vacuous `SecondPreimageResistantOn` when `valid := fun _ _ => false` does not imply
`TargetCollisionResistantOn id (xorTargetHash (fun _ => [])) validFixedLengthInput`, confirming
`hvalid` is necessary in `SecondPreimageResistantOn.targetCollisionResistantOn_xorTargetHash`. -/
theorem vacuous_spr_fails_without_hvalid :
    SecondPreimageResistantOn (fun _ => ([] : List Bool)) (fun _ _ => false) ∧
      ¬ TargetCollisionResistantOn id (xorTargetHash (fun _ => [])) validFixedLengthInput := by
  refine ⟨SecondPreimageResistantOn.of_injective (ComputableInPolyTime.const [])
    (fun _ _ _ _ hv _ => by contradiction), ?_⟩
  intro hTCR
  refine not_negligible_const one_ne_zero
    (negligible_of_eventually_le
      (hTCR.negligible sameLengthCollisionAdversary isPPT_sameLengthCollisionAdversary) ?_)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [eval_targetCollisionGame_const_sameLengthCollisionAdversary hn, Game.succProbability,
    PMF.pure_apply_self, ENNReal.toNNReal_one]

end CslibFrontierTests.Crypto.XorTargetHash
