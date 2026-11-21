/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SeededPackingRank

/-!
# Verifying seed balance from individual edge ranks

Each edge's rank counts all earlier members of its class. Every occupied class hence fits
within a proposed capacity exactly when every edge rank is below that capacity. The proof
embeds each fiber into the initial segment of ranks, which also handles empty fibers.
A fixed seed can then be checked locally using bounded rank guesses and individual bit claims.
-/

public section

namespace Cslib.PacketPacking.Seeded

open BalancedSchedules BitString

variable {E R C : Type*} [Fintype E] [LinearOrder E]
variable (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : E → R) (colOf : E → C)
  (seed : SeededLabels.Seed U (6 * a))

/-- The twice-average balance bound holds precisely when it holds at every edge's rank plus
one. An empty class has no ranks and contributes zero to its own occupancy inequality. -/
theorem balanced_iff_rank_succ_mul_le : Balanced U a vertex rowOf colOf seed ↔
    ∀ e, (rank U a vertex rowOf colOf seed e + 1) * 64 ^ (2 * a) ≤ 2 * Fintype.card E := by
  let ρ := fun r => label U a seed (vertex (.inl r))
  let κ := fun c => label U a seed (vertex (.inr c))
  let tag := pairLabel rowOf colOf ρ κ
  constructor
  · intro h e
    exact (Nat.mul_le_mul_right _ (classIndex_lt_occupancy rowOf colOf ρ κ e)).trans (h (tag e))
  · intro h γ
    let cap := 2 * Fintype.card E / 64 ^ (2 * a)
    have hD : 0 < 64 ^ (2 * a) := by positivity
    let index : {e // tag e = γ} → Fin cap := fun e =>
      ⟨rank U a vertex rowOf colOf seed e.val, (Nat.le_div_iff_mul_le hD).2 (h e.val)⟩
    have hinj : Function.Injective index := by
      intro e f he
      apply Subtype.ext
      exact classIndex_injective rowOf colOf ρ κ (e.property.trans f.property.symm)
        (congrArg Fin.val he)
    have hc := Fintype.card_le_of_injective index hinj
    rw [Fintype.card_fin] at hc
    exact (Nat.le_div_iff_mul_le hD).1 hc

/-- Any sound and complete rank-bit evaluator suffices to verify this seed. For each edge the
single bounded guess is shared by every verified bit. Width zero includes singleton graphs. -/
theorem balanced_iff_rank_bit_checks {width : ℕ} (hwidth : Fintype.card E ≤ 2 ^ width)
    (check : E → Fin width → Bool → Prop)
    (hcheck : ∀ e j b, check e j b ↔ (rank U a vertex rowOf colOf seed e).testBit j.val = b) :
    Balanced U a vertex rowOf colOf seed ↔ ∀ e, ∃ guess : Fin (2 ^ width),
      (guess.val + 1) * 64 ^ (2 * a) ≤ 2 * Fintype.card E ∧
      ∀ j : Fin width, check e j (guess.val.testBit j.val) := by
  rw [balanced_iff_rank_succ_mul_le]
  constructor
  · intro h e
    refine ⟨⟨_, (rank_lt_card U a vertex rowOf colOf seed e).trans_le hwidth⟩, h e, ?_⟩
    exact fun j => (hcheck e j _).2 rfl
  · intro h e
    obtain ⟨g, hg, hbits⟩ := h e
    have heq : g.val = rank U a vertex rowOf colOf seed e := by
      apply (eq_rank_iff_predecessor_bits U a vertex rowOf colOf seed e hwidth g.isLt).2
      rw [← rank_eq_sum_predecessors]
      exact fun j => ((hcheck e j _).1 (hbits j)).symm
    simpa only [heq] using hg

end Cslib.PacketPacking.Seeded
