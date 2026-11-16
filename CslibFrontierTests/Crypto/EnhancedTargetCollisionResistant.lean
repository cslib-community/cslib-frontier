/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Crypto.Computational.EnhancedTargetCollisionResistant
import CslibFrontier.Crypto.Computational.SecondPreimageResistant.Relations
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontierTests.Crypto.KeyedHashFixture

/-!
# Tests for enhanced target collision resistance

Checks for `CslibFrontier/Crypto/Computational/EnhancedTargetCollisionResistant.lean` as a
`module` client:

* Nonvacuity witnesses for `EnhancedTargetCollisionResistantOn` / `EnhancedTargetCollisionResistant`
  (`not_enhancedTargetCollisionResistant_snd_msg`, using `flipHeadBit` via
  `flipHeadEnhancedAdversary` to flip the first bit of an `(n + 1)`-bit key) and for
  `KeyedHashFamily.EnhancedTargetCollisionResistant`
  (`not_enhancedTargetCollisionResistant_zeroKeyedHashFamily`), plus positive nonvacuity for
  zero-length keys (`enhancedTargetCollisionResistant_zeroKey_id`).
* Concrete `appendKeyHash` and `isEnhancedTargetCollision` evaluations plus consumer examples
  composing `enhancedTargetCollisionResistant_zeroKey_id`,
  `TargetCollisionResistantOn.enhancedTargetCollisionResistantOn_appendKeyHash`,
  `EnhancedTargetCollisionResistantOn.targetCollisionResistantOn` (Exercise 8.27(d) of
  [BonehShoup2023], p. 354), and `HashFamily.targetCollisionResistant_toKeyedHashFamily`.
* Counterexamples checking pairs accepted when the `k'.length = keyLen n` check or the
  `valid n m'` check is omitted.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.EnhancedTargetCollisionResistant

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ## Nonvacuity witnesses and positive instance -/

/-- Explicit PPT adversary refuting `EnhancedTargetCollisionResistant` for `fun _ _ m => m` when
`keyLen n = n + 1`: apply `flipHeadBit` to `k` and return `(k', [])`. -/
noncomputable def flipHeadEnhancedAdversary : EnhancedTargetCollisionFinder where
  choose _ := pure ([], [])
  find _ _ key := pure (flipHeadBit key, [])

theorem isPPT_flipHeadEnhancedAdversary : flipHeadEnhancedAdversary.IsPPT where
  choose := (ComputableInPolyTime.const (([], []) : List Bool × List Bool)).isPPTOn
  find := by
    let E := encPair encUnary (encPair encBits encBits)
    have hk : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2) E encBits := by
      polytime
    exact ((computableInPolyTime_flipHeadBit.comp hk).prod
      (ComputableInPolyTime.const ([] : List Bool))).isPPTOn

/-- Nonvacuity witness for `EnhancedTargetCollisionResistant` and
`EnhancedTargetCollisionResistantOn` (at `valid := fun _ _ => true`): ignoring the key
(`H(k, m) := m`, `keyLen n := n + 1`) is broken with probability `1` by flipping the first bit of
`k` on `m₀ = m' = []`. -/
theorem not_enhancedTargetCollisionResistant_snd_msg :
    ¬ EnhancedTargetCollisionResistant (fun n => n + 1) (fun _ _ m => m) := by
  refine not_enhancedTargetCollisionResistantOn_of_eventually_le_succProbability one_ne_zero
    flipHeadEnhancedAdversary isPPT_flipHeadEnhancedAdversary
    (Filter.Eventually.of_forall fun n => ?_)
  have heval :
      ProbComp.eval (enhancedTargetCollisionGame (fun n => n + 1) (fun _ _ m => m)
        (fun _ _ => true) flipHeadEnhancedAdversary n) = PMF.pure true := by
    simp only [enhancedTargetCollisionGame, flipHeadEnhancedAdversary, ProbComp.eval_bind,
      ProbComp.eval_pure, pure_bind, BitString.eval_sampleList]
    trans (BitString.uniformList (n + 1)).bind fun _ => PMF.pure true
    · apply PMF.bind_congr_on_support; intro k hk
      have hkLen : k.length = n + 1 := BitString.length_of_mem_support_uniformList hk
      have hflipLen : (flipHeadBit k).length = n + 1 := by
        cases k with
        | nil => simp at hkLen
        | cons _ _ => simpa [flipHeadBit] using hkLen
      congr 1
      rw [isEnhancedTargetCollision_eq_true_iff]
      exact ⟨rfl, rfl, hflipLen, fun heq => flipHeadBit_ne_self k (Prod.mk.inj heq).1, rfl⟩
    · simp [PMF.bind_const]
  rw [heval, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]

noncomputable def zeroKeyedFinder : EnhancedTargetCollisionFinder where
  choose _ := pure ([], [])
  find _ _ key := pure (key, [true])

theorem isPPT_zeroKeyedFinder : zeroKeyedFinder.IsPPT where
  choose := (ComputableInPolyTime.const (([], []) : List Bool × List Bool)).isPPTOn
  find := by
    let E := encPair encUnary (encPair encBits encBits)
    have hk : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2) E encBits := by
      polytime
    exact (hk.prod (ComputableInPolyTime.const ([true] : List Bool))).isPPTOn

/-- Nonvacuity witness for `KeyedHashFamily.EnhancedTargetCollisionResistant` using the shared
constant `zeroKeyedHashFamily`. -/
theorem not_enhancedTargetCollisionResistant_zeroKeyedHashFamily :
    ¬ zeroKeyedHashFamily.EnhancedTargetCollisionResistant := by
  refine not_enhancedTargetCollisionResistantOn_of_eventually_le_succProbability one_ne_zero
    zeroKeyedFinder isPPT_zeroKeyedFinder (Filter.Eventually.of_forall fun n => ?_)
  have heval :
      ProbComp.eval (enhancedTargetCollisionGame zeroKeyedHashFamily.keyLen
        zeroKeyedHashFamily.eval (fun _ _ => true) zeroKeyedFinder n) = PMF.pure true := by
    simp only [enhancedTargetCollisionGame, zeroKeyedFinder, zeroKeyedHashFamily_keyLen,
      ProbComp.eval_bind, ProbComp.eval_pure, pure_bind, BitString.eval_sampleList]
    trans (BitString.uniformList n).bind fun _ => PMF.pure true
    · apply PMF.bind_congr_on_support; intro k hk
      have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
      congr 1
      rw [isEnhancedTargetCollision_eq_true_iff]
      refine ⟨rfl, rfl, hkLen, ?_, rfl⟩
      intro heq
      have hnil : ([] : List Bool) = [true] := (Prod.mk.inj heq).2.symm
      cases hnil
    · simp [PMF.bind_const]
  rw [heval, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]

/-- Positive nonvacuity: when keys have length `0`, the identity function `H(k, m) := m` IS
unconditionally enhanced target collision-resistant. -/
theorem enhancedTargetCollisionResistant_zeroKey_id :
    EnhancedTargetCollisionResistant (fun _ => 0) (fun _ _ m => m) := by
  apply EnhancedTargetCollisionResistantOn.of_negligible
  intro adversary _
  have heval (n : ℕ) :
      ProbComp.eval (enhancedTargetCollisionGame (fun _ => 0) (fun _ _ m => m)
        (fun _ _ => true) adversary n) = PMF.pure false := by
    simp only [enhancedTargetCollisionGame, ProbComp.eval_bind, ProbComp.eval_pure]
    trans (ProbComp.eval (adversary.choose n)).bind fun _ => PMF.pure false
    · apply PMF.bind_congr_on_support; intro choice _
      trans (BitString.uniformList 0).bind fun _ => PMF.pure false
      · rw [BitString.eval_sampleList]
        apply PMF.bind_congr_on_support; intro k hk
        have hk0 : k = [] := List.eq_nil_of_length_eq_zero
          (BitString.length_of_mem_support_uniformList hk)
        trans (ProbComp.eval (adversary.find n choice.2 k)).bind fun _ => PMF.pure false
        · apply PMF.bind_congr_on_support; intro ans _
          congr 1
          rw [Bool.eq_false_iff]
          intro hcol
          obtain ⟨_, _, hk'0, hne, hm_eq⟩ := isEnhancedTargetCollision_eq_true_iff.mp hcol
          exact hne (Prod.ext ((List.eq_nil_of_length_eq_zero hk'0).trans hk0.symm) hm_eq)
        · simp [PMF.bind_const]
      · simp [PMF.bind_const]
    · simp [PMF.bind_const]
  simp only [heval, Game.succProbability, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte,
    ENNReal.toNNReal_zero, negligible_zero]

/-! ## Concrete checks and consumer compositions -/

/-- Concrete evaluation of `appendKeyHash`. -/
example :
    appendKeyHash (fun _ _ m => m) 2 [true, false] [true] = [true, true, false] := rfl

/-- Distinct keys collide for `H(k, m) := m`, accepted when `k'` has length `keyLen n`. -/
example :
    isEnhancedTargetCollision id (fun _ _ m => m) (fun _ _ => true) 2
      [false, true] [true] [true, true] [true] = true := by
  decide

/-- Identical `(k', m') = (k, m₀)` is not an enhanced target collision. -/
example :
    isEnhancedTargetCollision id (fun _ _ m => m) (fun _ _ => true) 2
      [false, true] [true] [false, true] [true] = false := by
  decide

/-- Appending the key blocks cross-key collisions in `isEnhancedTargetCollision`. -/
example :
    isEnhancedTargetCollision id (appendKeyHash (fun _ _ m => m)) (fun _ _ => true) 2
      [false, true] [true] [true, true] [true] = false := by
  decide

/-- Concrete consumer composition: `appendKeyHash` preserves `TargetCollisionResistant` for the
zero-length-key identity `enhancedTargetCollisionResistant_zeroKey_id`. -/
theorem targetCollisionResistant_appendKeyHash_zeroKey_id :
    TargetCollisionResistant (fun _ => 0) (appendKeyHash (fun _ _ m => m)) :=
  EnhancedTargetCollisionResistantOn.targetCollisionResistantOn
    (TargetCollisionResistantOn.enhancedTargetCollisionResistantOn_appendKeyHash
      (EnhancedTargetCollisionResistantOn.targetCollisionResistantOn
        enhancedTargetCollisionResistant_zeroKey_id))

/-- Composing `HashFamily.targetCollisionResistant_toKeyedHashFamily`, Exercise 8.27(d), and
`KeyedHashFamily.EnhancedTargetCollisionResistant.targetCollisionResistant` preserves
`KeyedHashFamily.TargetCollisionResistant`. -/
theorem targetCollisionResistant_appendKeyHash_of_hashFamily
    {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    hH.toKeyedHashFamily.appendKeyHash.TargetCollisionResistant :=
  hH.targetCollisionResistant_toKeyedHashFamily
    |>.enhancedTargetCollisionResistant_appendKeyHash
    |>.targetCollisionResistant

/-! ## Hypothesis necessity counterexamples -/

/-- Counterexample 1 (explicit `(k', m')` pair when `k'.length == keyLen n` is omitted):
for every `k` of length `n + 1`, taking `m₀ := []`, `k' := []`, and `m' := k` satisfies
`(k, m₀) ≠ (k', m')` and
`appendKeyHash (fun _ _ m => m) n k' m' = appendKeyHash (fun _ _ m => m) n k m₀`.
Without the `k'.length = keyLen n` check, an adversary can break Exercise 8.27(d) on the
unconditionally TCR hash `H(k, m) := m` by returning `k' = []`, `m' = k` on `(n + 1)`-bit keys. -/
theorem counterexample_missing_keyLen_check (n : ℕ) (k : List Bool) (hk : k.length = n + 1) :
    (k, ([] : List Bool)) ≠ ([], k) ∧
      appendKeyHash (fun _ _ m => m) n [] k = appendKeyHash (fun _ _ m => m) n k [] := by
  refine ⟨?_, ?_⟩
  · intro heq
    have hk0 : k = [] := (Prod.mk.inj heq).1
    simp [hk0] at hk
  · simp [appendKeyHash]

/-- Counterexample 2 (explicit `(k', m')` pair when `valid n m'` is omitted):
taking `H(k, m) := m.take 1`, `m₀ := [false]`, and `m' := [false, false]` with `k' := k`, checks
that `m₀` has length `1`, `(k, m₀) ≠ (k, m')`, and
`appendKeyHash H n k m' = appendKeyHash H n k m₀`.
Without the `valid n m'` check, an adversary can break Exercise 8.27(d) on the injective (hence
TCR) family `m ↦ m.take 1` over `valid n m := (m.length == 1)` even with `k' = k`. -/
theorem counterexample_missing_valid_check (n : ℕ) (k : List Bool) :
    let H : ℕ → List Bool → List Bool → List Bool := fun _ _ m => m.take 1
    let m₀ : List Bool := [false]
    let m' : List Bool := [false, false]
    m₀.length = 1 ∧ (k, m₀) ≠ (k, m') ∧ appendKeyHash H n k m' = appendKeyHash H n k m₀ := by
  simp [appendKeyHash]

end CslibFrontierTests.Crypto.EnhancedTargetCollisionResistant
