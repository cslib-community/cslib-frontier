/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootRankTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ScheduleFields

/-!
# Source-clock bound for schedule-tree initialization

The parameter record consists of a binary half-length, binary precision, requested bit and sign.
Its length is logarithmic in the source clock for each fixed number of tapes. A fixed polynomial
in this length and the actual lengths of both output fields fit in the block-count budget.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing.MultiTapeATM Circuits.Boolean.CarryLookahead.Query

/-- The short request for a signed bit of the padded source count. -/
@[expose] def scheduleRequest (k t bit : ℕ) (claim : Bool) : CountingInput.Input :=
  ⟨(k + 1) * numBlocks t, ⟨paddedTime t + 1, bit, claim⟩⟩

/-- The native cost of installing all outer fields is linear in the standard block count. -/
theorem exists_scheduleField_clock (k c d : ℕ) :
    ∃ K, ∀ {t : ℕ}, 2 ≤ t → ∀ (bit : Fin (paddedTime t + 1)) (claim : Bool),
      c * (ScheduleFields.budget d (scheduleRequest k t bit.val claim) + 1) ≤
        K * (numBlocks t + 1) := by
  let P (n : ℕ) := (2 * ((k + 1).size + n) + 4 * (2 + n) + 5) ^ d
  have hp : Cslib.PolynomiallyBounded P := by unfold P; fun_prop
  obtain ⟨A, D, hA⟩ := Cslib.polynomiallyBounded_iff_le.mp hp
  obtain ⟨B, hB⟩ := exists_size_pow_le_numBlocks D
  refine ⟨c * (A * B + (k + 1) + 1), ?_⟩
  intro t ht bit claim
  let u := (t + 2).size
  let a := scheduleRequest k t bit.val claim
  have hq : numBlocks t ≤ t + 2 := by
    have h := numBlocks_le_div_sqrt_log_add_one t
    have h' := Nat.div_le_self t (Nat.log 2 (t + 2)).sqrt
    omega
  have hhalf : a.count.size ≤ (k + 1).size + u :=
    (Nat.size_mul_le _ _).trans (Nat.add_le_add_left (Nat.size_le_size hq) _)
  have hw : a.query.width.size ≤ 2 + u := by
    have h := (Nat.size_le_size (paddedTime_add_one_le ht)).trans (Nat.size_mul_le 2 t)
    change (paddedTime t + 1).size ≤ 2 + u
    change (paddedTime t + 1).size ≤ 2 + t.size at h
    exact h.trans (Nat.add_le_add_left (Nat.size_le_size (by omega : t ≤ t + 2)) 2)
  have hlen := CountingInput.length_encInput_le a bit.isLt
  have hpoly : ((CountingInput.encInput a).length + 1) ^ d ≤ A * B * (numBlocks t + 1) := by
    calc
      _ ≤ P u := Nat.pow_le_pow_left (by omega) _
      _ ≤ _ := by rw [Nat.mul_assoc]; exact (hA _).trans (Nat.mul_le_mul_left A (hB t))
  have hraw : a.count ≤ (k + 1) * (numBlocks t + 1) :=
    Nat.mul_le_mul_left _ (Nat.le_succ _)
  change c * (((CountingInput.encInput a).length + 1) ^ d + a.count + 1) ≤ _
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

end Cslib.Complexity.CountingSimulation
