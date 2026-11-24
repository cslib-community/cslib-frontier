/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Crypto.Computational.ShoupComposition
import CslibFrontier.Crypto.Computational.InaccessibleEntropy.TargetCollision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Module-client tests for `ShoupComposition` and compact-key `rompelCompression`

Exercises the exported `module` surface of `CslibFrontier.Crypto.Computational.ShoupComposition`
and `CslibFrontier.Crypto.Computational.InaccessibleEntropy.TargetCollision`: concrete evaluation
of `shoupComposeEval`, planted-input and uniform-pushforward properties of `shoupPackMasks`,
finite-`n` loss (`dyadicSize 3 = 4`) of `succProbability_targetCollisionGame_shoupCompose_le` on a
concrete XOR compression step, `isPPT_shoupComposeAdversary`, and the end-to-end `(Nat.log 2 n + 1)`
shrinkage and `O(|y| log t)` key-length bounds (`rompelCompression_keyLen_le`,
`OneWay.exists_shrinkingCollisionGrid_rompelCompression`).
-/

-- This regression module intentionally exports no declarations.

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

-- Concrete evaluation of `shoupComposeKeyLen` and `shoupComposeEval` through the public
-- `@[expose]` cascade surface (`b = 2, s = 1, t = 3, baseKeyLen = 2`, key length `2 + 4 = 6`):
example :
    let h : ℕ → List Bool → List Bool → List Bool :=
      fun _ k w => [k.headD false != w.headD false, w.getD 1 false != w.getD 2 false]
    shoupComposeKeyLen (fun _ => 2) (fun _ => 2) (fun _ => 3) 0 = 6 ∧
      shoupComposeEval (fun _ => 2) (fun _ => 2) (fun _ => 1) (fun _ => 3) h 0
        [true, false, false, true, true, false] [true, true, false, true, true] = [true, true] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv1 : padicValNat 2 1 = 0 := by
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 1)]
  have hv2 : padicValNat 2 2 = 1 := by
    rw [Nat.padicValNat_def, Nat.Prime.multiplicity_self]
  have hv3 : padicValNat 2 3 = 0 := by
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
  refine ⟨by decide, ?_⟩
  dsimp only [shoupComposeEval, shoupCascade, shoupState, shoupStepInput, shoupChunk]
  rw [hv1, hv2, hv3]
  decide

-- Planted step-input recovery and uniform mask distribution on concrete 3-to-2 XOR compression:
example :
    let step : List Bool → List Bool :=
      fun w => BitString.listXor 2 [w.take 2, w.drop 2]
    let x := [true, false, true, true, false]
    let T := [false, true, true, false]
    let masks := shoupPackMasks 2 1 3 2 step x T
    shoupStepInput 2 1 masks x 2 (shoupState 2 1 step masks x 1) =
        BitString.listRow 2 (padicValNat 2 2) T ++ shoupChunk 2 1 2 x ∧
      (BitString.uniformList (shoupMasksLen 2 3)).map (shoupPackMasks 2 1 3 2 step x) =
        BitString.uniformList 4 :=
  ⟨shoupStepInput_shoupPackMasks _ (fun _ _ => BitString.length_listXor _ _)
      (by decide) (by decide) _ _,
    uniformList_map_shoupPackMasks 2 1 3 2 _ (fun _ _ => BitString.length_listXor _ _)
      (by decide) (by decide) _⟩

-- Concrete finite-`n` reduction bound (`dyadicSize 3 = 4`) and `IsPPT` preservation on an explicit
-- keyed `3 → 2`-bit XOR step family:
example (adversary : TargetCollisionFinder) (ha : adversary.IsPPT) :
    let h : ℕ → List Bool → List Bool → List Bool :=
      fun _ k w => BitString.listXor 2 [BitString.listRow 2 0 k, w.take 2, w.drop 2]
    (shoupComposeAdversary (fun _ => 2) (fun _ => 2) (fun _ => 1) (fun _ => 3) h adversary).IsPPT ∧
      Game.succProbability
        (ProbComp.eval
          (targetCollisionGame
            (shoupComposeKeyLen (fun _ => 2) (fun _ => 2) (fun _ => 3))
            (shoupComposeEval (fun _ => 2) (fun _ => 2) (fun _ => 1) (fun _ => 3) h)
            (fun _ x => x.length == 5) adversary 0)) ≤
        4 * Game.succProbability
          (ProbComp.eval
            (targetCollisionGame (fun _ => 2) h (fun _ w => w.length == 3)
              (shoupComposeAdversary (fun _ => 2) (fun _ => 2) (fun _ => 1) (fun _ => 3)
                h adversary) 0)) := by
  intro h
  have hh : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => h p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits := by
    let pid := ComputableInPolyTime.id' (encIn := encKeyedInput encBits)
    have hk := ComputableInPolyTime.bitsRowWithInput (.const 2) (.const 0) pid.snd'.fst'
    have hw1 := ComputableInPolyTime.bitsTakeWithInput pid.snd'.snd' (.const 2)
    have hw2 := ComputableInPolyTime.bitsDropWithInput pid.snd'.snd' (.const 2)
    exact ComputableInPolyTime.bitsXorWithInput (.const 2)
      (ComputableInPolyTime.cons' hk
        (ComputableInPolyTime.cons' hw1 (ComputableInPolyTime.cons' hw2 (.const []))))
  refine ⟨isPPT_shoupComposeAdversary (.const 2) (.const 2) (.const 1) (.const 3) hh
      (fun _ _ _ _ _ => BitString.length_listXor _ _) ha, ?_⟩
  have hbound := succProbability_targetCollisionGame_shoupCompose_le
    (baseKeyLen := fun _ => 2) (outLen := fun _ => 2) (s := fun _ => 1)
    (t := fun _ => 3) (L := fun _ => 5) (h := h)
    adversary 0 (by decide) (by decide) (by decide) (fun _ _ _ _ => BitString.length_listXor _ _)
  have hdyad : (dyadicSize 3 : ℝ≥0) = 4 := by
    have : dyadicSize 3 = 4 := by decide
    exact_mod_cast this
  rw [hdyad] at hbound
  exact hbound

-- Module-client check of `rompelCompression_keyLen_le` and the end-to-end `OneWay` compression
-- theorem preserving `(Nat.log 2 n + 1)`-bit candidate shrinkage and `O(|y| log t)` keys:
example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ G : ShrinkingCollisionGrid,
      (∀ n, G.shrinkLen n = Nat.log 2 n + 1) ∧
      (rompelCompression G).TargetCollisionResistant ∧
      ∀ n, (rompelCompression G).keyLen n ≤
        (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n :=
  hf.exists_shrinkingCollisionGrid_rompelCompression
