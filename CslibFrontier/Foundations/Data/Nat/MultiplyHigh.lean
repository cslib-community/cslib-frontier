/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat

/-!
# Fibres of multiplication followed by integer division

The map `u ↦ u * d / M` sends integers below `M` into the range below `d`. Each fibre has
between `M / d` and `M / d + 1` elements. This is the integer arithmetic behind multiply-high
sampling; it differs from reduction modulo `d` in the placement of the larger fibres.

## Main results

* `Nat.card_mul_div_fiber`: the exact fibre size as a difference of ceiling divisions.
* `Nat.card_mul_div_fiber_bounds`: the lower and upper fibre counts.
-/

public section

namespace Nat

/-- Multiplication followed by division maps an input below `M` into the range below `d`. -/
theorem mul_div_lt_of_lt {M d u : ℕ} (hM : 0 < M) (hd : 0 < d) (hu : u < M) :
    u * d / M < d := by
  rw [Nat.div_lt_iff_lt_mul hM]
  exact (Nat.mul_lt_mul_of_pos_right hu hd).trans_eq (Nat.mul_comm M d)

private theorem mul_div_eq_iff {M d k u : ℕ} (hM : 0 < M) (hd : 0 < d) :
    u * d / M = k ↔ (k * M) ⌈/⌉ d ≤ u ∧ u < ((k + 1) * M) ⌈/⌉ d := by
  rw [ceilDiv_le_iff_le_mul hd, ← not_le, ceilDiv_le_iff_le_mul hd, not_le, Nat.mul_comm d u,
    ← Nat.le_div_iff_mul_le hM, ← Nat.div_lt_iff_lt_mul hM]
  omega

/-- The fibre of `u ↦ u * d / M` over `k < d` is the interval between consecutive scaled
ceiling divisions. -/
theorem card_mul_div_fiber {M d : ℕ} (hM : 0 < M) (hd : 0 < d) (k : Fin d) :
    Nat.card {u : Fin M // u.val * d / M = k.val} =
      (((k.val + 1) * M) ⌈/⌉ d) - ((k.val * M) ⌈/⌉ d) := by
  have hupper : ((k.val + 1) * M) ⌈/⌉ d ≤ M :=
    (ceilDiv_le_iff_le_mul hd).mpr (Nat.mul_le_mul_right M k.isLt)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.card_map (f := Fin.valEmbedding)]
  have hfiber : (Finset.univ.filter (fun u : Fin M => u.val * d / M = k.val)).map
      Fin.valEmbedding = Finset.Ico ((k.val * M) ⌈/⌉ d) (((k.val + 1) * M) ⌈/⌉ d) := by
    ext u
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    exact ⟨fun ⟨_, hv, h⟩ => h ▸ (mul_div_eq_iff hM hd).mp hv,
      fun hu => ⟨⟨u, hu.2.trans_le hupper⟩, (mul_div_eq_iff hM hd).mpr hu, rfl⟩⟩
  rw [hfiber, Nat.card_Ico]

/-- Every multiply-high fibre has either the floor-size count or at most one more input. -/
theorem card_mul_div_fiber_bounds {M d : ℕ} (hM : 0 < M) (hd : 0 < d) (k : Fin d) :
    M / d ≤ Nat.card {u : Fin M // u.val * d / M = k.val} ∧
      Nat.card {u : Fin M // u.val * d / M = k.val} ≤ M / d + 1 := by
  rw [card_mul_div_fiber hM hd k, Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
  let A := k.val * M + (d - 1)
  have h0 : k.val * M + d - 1 = A := by omega
  have h1 : (k.val + 1) * M + d - 1 = A + M := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [h0, h1, Nat.add_div hd]
  split_ifs <;> simp [Nat.add_assoc]

end Nat
