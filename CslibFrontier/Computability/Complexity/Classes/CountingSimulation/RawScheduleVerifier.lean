/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RawScheduleSum
public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OuterSumTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveWordSum

/-!
# A native outer schedule sum at the source clock

Starting at the prepared root, a finite machine finishes the padded accepting-path count if its
leaf continuation checks bits of the actual schedule contractions. This accounts for every
movement-word path, the finishing adder and the carry-save descent.
-/

public section

namespace Cslib.Complexity.CountingSimulation.RawScheduleSum

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM

/-- The two carry-save operand words for a raw path through the outer sum at full precision. -/
@[expose] noncomputable def contractionLeaf {k s : ℕ} {State : Type} (M : MultiTapePTM k Bool State)
    (e : State ≃ Fin s) (input : List Bool) (t : ℕ) (path : List Bool) :=
  operand (paddedTime t + 1) (weight (fun σ : Schedule k (numBlocks t) =>
    (M.explicitBlockNetwork input (blockLength t) σ e).contraction) path)

/-- Conditional outer stage of the simulation. From prepared tapes and a native contraction-bit
leaf, a fixed alternating machine checks the padded count bit within one leaf clock plus
`O(numBlocks t + 1)`. The statement quantifies the source clock after the simulator and constant. -/
theorem exists_count_verifier_of_contraction_leaf {k a : ℕ} {S : Type} [Finite S]
    (leaf : Bool → Bool → MultiTapeATM (a + 12) Bool S) :
    ∃ (r q : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size a r q) Bool Q) (K : ℕ),
      ∀ {s : ℕ} {State : Type} [Finite State] (M : MultiTapePTM k Bool State) (e : State ≃ Fin s)
        (input context : List Bool) {t : ℕ}, 2 ≤ t → ∀ (leafTime : ℕ),
        let n := 2 ^ (2 * (k + 1) * numBlocks t)
        let w := paddedTime t + 1
        let budget := CarrySaveCountingRoot.sizeBudget n w
        let scratch := CarrySaveLeaf.scratch a context (encNat n) (encNat w)
        CarrySaveStream.LeafBound leaf leafTime budget input scratch →
        CarrySaveStream.LeafCorrect (contractionLeaf M e input t) leaf leafTime budget
          input scratch →
        ∀ (bit : Fin w) (claim : Bool),
          let cfg := CarryLookaheadCounting.initial a r q input context n w bit.val claim
          let start := cfg.withState (some atm.toPTM.initial)
          let time := K * (numBlocks t + 1) + leafTime
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            (M.acceptCount input (paddedTime t)).testBit bit.val = claim) := by
  obtain ⟨r, q, Q, hQ, atm, c, d, h⟩ := CarrySaveWordSum.exists_finisher leaf
  obtain ⟨K, hK⟩ := exists_outerSum_clock k c d
  refine ⟨r, q, Q, hQ, atm, K, ?_⟩
  intro s State _ M e input context t ht time n w budget scratch htime hleaf bit claim
  obtain ⟨hh, ha⟩ := h input context (2 * (k + 1) * numBlocks t) w time
    (contractionLeaf M e input t) htime hleaf bit claim
  change (_ ↔ total w (fun σ : Schedule k (numBlocks t) =>
    (M.explicitBlockNetwork input (blockLength t) σ e).contraction) bit = claim) at ha
  rw [total_contraction_apply M e input ht] at ha
  have hb := hK ht time
  exact ⟨hh.mono hb,
    ⟨fun hacc => ha.mp (hacc.of_halted_stepCoins hh), fun heq => (ha.mpr heq).mono hb⟩⟩

end Cslib.Complexity.CountingSimulation.RawScheduleSum
