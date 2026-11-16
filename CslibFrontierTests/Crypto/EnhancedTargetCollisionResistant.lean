/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Crypto.Computational.EnhancedTargetCollisionResistant
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for enhanced target collision resistance

Checks for `CslibFrontier/Crypto/Computational/EnhancedTargetCollisionResistant.lean` as a
`module` client:

* Nonvacuity witnesses for `EnhancedTargetCollisionResistantOn` / `EnhancedTargetCollisionResistant`
  (`not_enhancedTargetCollisionResistant_snd_msg`, using `flipHeadEnhancedAdversary` to flip the
  first bit of an `(n + 1)`-bit key) and for `KeyedHashFamily.EnhancedTargetCollisionResistant`
  (`not_enhancedTargetCollisionResistant_zeroKeyedHashFamily`), plus positive nonvacuity for
  zero-length keys (`enhancedTargetCollisionResistant_zeroKey_id`).
* Consumer examples for `EnhancedTargetCollisionResistantOn`, `KeyedHashFamily`, and
  `TargetCollisionResistantOn.enhancedTargetCollisionResistantOn_appendKeyHash` (Exercise 8.27(d)
  of [BonehShoup2023], p. 354), along with concrete checks of
  `eval_enhancedTargetCollisionGame_toEnhancedFinder` and
  `succProbability_enhancedTargetCollisionGame_appendKeyHash_le`.
* Hypothesis-necessity counterexamples for omitting `k'.length = keyLen n` and omitting
  `valid n m'`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.EnhancedTargetCollisionResistant

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ## Nonvacuity witnesses and positive instance -/

/-- Explicit PPT adversary refuting `EnhancedTargetCollisionResistant` for `fun _ _ m => m` when
`keyLen n = n + 1`: flip the first bit of `k` and return `(k', [])`. -/
noncomputable def flipHeadEnhancedAdversary : EnhancedTargetCollisionFinder where
  choose _ := pure ([], [])
  find _ _ key := pure (match key with | b :: rest => (!b) :: rest | [] => [], [])

theorem isPPT_flipHeadEnhancedAdversary : flipHeadEnhancedAdversary.IsPPT where
  choose := (ComputableInPolyTime.const (([], []) : List Bool × List Bool)).isPPTOn
  find := by
    let E := encPair encUnary (encPair encBits encBits)
    have hk : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2) E encBits := by
      polytime
    have hflip : ComputableInPolyTime
        (fun k : List Bool => match k with | b :: rest => (!b) :: rest | [] => [])
        encBits encBits := by
      have h : (fun k : List Bool => match k with | b :: rest => (!b) :: rest | [] => []) =
          fun k => if k.isEmpty then [] else (!(k.headD false)) :: k.tail := by
        funext k; cases k <;> rfl
      rw [h]
      polytime
    exact ((hflip.comp hk).prod (ComputableInPolyTime.const ([] : List Bool))).isPPTOn

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
      cases k with
      | nil => simp at hkLen
      | cons b rest =>
        congr 1
        rw [isEnhancedTargetCollision_eq_true_iff]
        refine ⟨rfl, rfl, hkLen, ?_, rfl⟩
        intro heq
        have hb : b = !b := (List.cons.inj (Prod.mk.inj heq).1).1.symm
        cases b <;> cases hb
    · simp [PMF.bind_const]
  rw [heval, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]

/-- Minimal `KeyedHashFamily` mapping every message to `0^n`, refuting
`KeyedHashFamily.EnhancedTargetCollisionResistant` for `assumptions.md` nonvacuity. -/
def zeroKeyedHashFamily : KeyedHashFamily where
  keyLen := id
  digestLen := id
  eval n _ _ := List.replicate n false
  keyLen_polyTime := ComputableInPolyTime.id'
  digestLen_polyTime := ComputableInPolyTime.id'
  polyTime := by polytime
  le_digestLen _ := le_rfl
  length_eq _ _ _ _ := List.length_replicate

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

/-- Nonvacuity witness for `KeyedHashFamily.EnhancedTargetCollisionResistant`. -/
theorem not_enhancedTargetCollisionResistant_zeroKeyedHashFamily :
    ¬ zeroKeyedHashFamily.EnhancedTargetCollisionResistant := by
  refine not_enhancedTargetCollisionResistantOn_of_eventually_le_succProbability one_ne_zero
    zeroKeyedFinder isPPT_zeroKeyedFinder (Filter.Eventually.of_forall fun n => ?_)
  have heval :
      ProbComp.eval (enhancedTargetCollisionGame zeroKeyedHashFamily.keyLen
        zeroKeyedHashFamily.eval (fun _ _ => true) zeroKeyedFinder n) = PMF.pure true := by
    simp only [enhancedTargetCollisionGame, zeroKeyedFinder, zeroKeyedHashFamily,
      ProbComp.eval_bind, ProbComp.eval_pure, pure_bind, BitString.eval_sampleList, id_eq]
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

/-! ## Consumer bridges and API checks -/

/-- Any `HashFamily` yields an `EnhancedTargetCollisionResistant` `KeyedHashFamily` via
`appendKeyHash`. -/
example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    hH.toKeyedHashFamily.appendKeyHash.EnhancedTargetCollisionResistant :=
  hH.targetCollisionResistant_toKeyedHashFamily.enhancedTargetCollisionResistant_appendKeyHash

/-- Any `KeyedHashFamily` that is `EnhancedTargetCollisionResistant` is `TargetCollisionResistant`
via `KeyedHashFamily.EnhancedTargetCollisionResistant.targetCollisionResistant`. -/
example {H : KeyedHashFamily} (hH : H.EnhancedTargetCollisionResistant) :
    H.TargetCollisionResistant :=
  hH.targetCollisionResistant

/-- Round-trip on `TargetCollisionResistantOn`, concrete game bounds, and `.negligible`. -/
example {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (hTCR : TargetCollisionResistantOn keyLen H valid)
    (advE : EnhancedTargetCollisionFinder) (hEPPT : advE.IsPPT)
    (advT : TargetCollisionFinder) (n : ℕ) :
    TargetCollisionResistantOn keyLen (appendKeyHash H) valid ∧
      Negligible (fun m => Game.succProbability (ProbComp.eval
        (enhancedTargetCollisionGame keyLen (appendKeyHash H) valid advE m))) ∧
      Game.succProbability (ProbComp.eval
        (enhancedTargetCollisionGame keyLen (appendKeyHash H) valid advE n)) ≤
        Game.succProbability (ProbComp.eval
          (targetCollisionGame keyLen H valid (toTargetFinder advE) n)) ∧
      ProbComp.eval
          (enhancedTargetCollisionGame keyLen H valid (toEnhancedFinder advT) n) =
        ProbComp.eval (targetCollisionGame keyLen H valid advT n) :=
  ⟨hTCR.enhancedTargetCollisionResistantOn_appendKeyHash.targetCollisionResistantOn,
    hTCR.enhancedTargetCollisionResistantOn_appendKeyHash.negligible advE hEPPT,
    succProbability_enhancedTargetCollisionGame_appendKeyHash_le keyLen H valid advE n,
    eval_enhancedTargetCollisionGame_toEnhancedFinder keyLen H valid advT n⟩

/-! ## Hypothesis necessity counterexamples -/

/-- Counterexample 1 (omitting `k'.length == keyLen n` invalidates Exercise 8.27(d)):
for every `k` of length `n + 1`, taking `m₀ := []`, `k' := []`, and `m' := k` satisfies
`(k, m₀) ≠ (k', m')` and
`appendKeyHash (fun _ _ m => m) n k' m' = appendKeyHash (fun _ _ m => m) n k m₀`.
In prose, `H(k, m) := m` is unconditionally TCR, so omitting `k'.length = keyLen n` allows an
adversary to return `k' = []`, `m' = k` on `H'(k, m) = m ++ k` for every `(n + 1)`-bit key `k`. -/
theorem counterexample_missing_keyLen_check (n : ℕ) (k : List Bool) (hk : k.length = n + 1) :
    (k, ([] : List Bool)) ≠ ([], k) ∧
      appendKeyHash (fun _ _ m => m) n [] k = appendKeyHash (fun _ _ m => m) n k [] := by
  refine ⟨?_, ?_⟩
  · intro heq
    have hk0 : k = [] := (Prod.mk.inj heq).1
    simp [hk0] at hk
  · simp [appendKeyHash]

/-- Counterexample 2 (omitting `valid n m'` invalidates Exercise 8.27(d)):
taking `H(k, m) := m.take 1`, `m₀ := [false]`, and `m' := [false, false]` with `k' := k`, checks
that `m₀` has length `1`, `(k, m₀) ≠ (k, m')`, and
`appendKeyHash H n k m' = appendKeyHash H n k m₀`.
In prose, `m ↦ m.take 1` is injective—and therefore TCR—on `valid n m := (m.length == 1)`, so
accepting an invalid `m'` (`m'.length ≠ 1`) would break `appendKeyHash H` even with `k' = k`. -/
theorem counterexample_missing_valid_check (n : ℕ) (k : List Bool) :
    let H : ℕ → List Bool → List Bool → List Bool := fun _ _ m => m.take 1
    let m₀ : List Bool := [false]
    let m' : List Bool := [false, false]
    m₀.length = 1 ∧ (k, m₀) ≠ (k, m') ∧ appendKeyHash H n k m' = appendKeyHash H n k m₀ := by
  simp [appendKeyHash]

end CslibFrontierTests.Crypto.EnhancedTargetCollisionResistant
