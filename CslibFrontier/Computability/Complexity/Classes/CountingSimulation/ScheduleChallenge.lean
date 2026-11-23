/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.ScheduleFieldClock
public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OuterRootTemplate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordLoad

/-!
# Encoding a signed count-bit challenge for a clocked source

The external metadata consists of the original binary time, binary bit index and sign.
Computing both short initialization words costs a polynomial in the length of this record.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeATM ComputableInPolyTime
open Circuits.Boolean.CarryLookahead.Query

/-- The original source clock and the signed bit requested by the caller. -/
structure ScheduleChallenge where
  /-- Source time before padding to a whole number of blocks. -/
  time : ℕ
  /-- Least-significant-first accepting count index. -/
  bit : ℕ
  /-- Required truth value of the indexed bit. -/
  claim : Bool
  deriving DecidableEq

namespace ScheduleChallenge

/-- The two numeric fields are framed binary words. The sign occupies one bit. -/
enc_structure enc : ScheduleChallenge where time : encNat, bit : encNat, claim : encBool

theorem length_enc (p : ScheduleChallenge) :
    (enc p).length = 2 * p.time.size + 2 * p.bit.size + 3 := by
  simp [enc_apply, encFields, encBool_apply, encNat_apply, ← Nat.size_eq_bits_len]
  omega

/-- Derive the raw schedule half-length, precision, selected bit and sign on the machine. -/
theorem request_polyTime (k : ℕ) :
    ComputableInPolyTime (fun p : ScheduleChallenge => scheduleRequest k p.time p.bit p.claim)
      enc CountingInput.encInput := by
  have ht : ComputableInPolyTime ScheduleChallenge.time enc encNat := by fun_prop
  have hq := binary_numBlocks.comp ht
  have hp := binary_mul' hq (binary_blockLength.comp ht)
  apply CountingInput.encInput_mk_polyTime
  · exact binary_mul' (const (k + 1)) hq
  · apply Initial.encInput_mk_polyTime
    · exact binary_add' hp (const 1)
    · fun_prop
    · fun_prop

/-- Put both short projections under the same input-length bound. -/
theorem exists_setup_degree (k states : ℕ) :
    ∃ d, let T := fun p : ScheduleChallenge => ((enc p).length + 1) ^ d
      ComputableInO (fun p : ScheduleChallenge => outerRootTemplate k states p.time)
        enc RootBalanceRequest.encPublic T T ∧
      ComputableInO (fun p : ScheduleChallenge => scheduleRequest k p.time p.bit p.claim)
        enc CountingInput.encInput T T := by
  have ht : ComputableInPolyTime ScheduleChallenge.time enc encNat := by fun_prop
  obtain ⟨a, b, hf⟩ := ((computableInPolyTime_outerRootTemplate k states).comp ht).exists_degree
  obtain ⟨d, e, hg⟩ := (request_polyTime k).exists_degree
  refine ⟨a + d, hf.inO.mono_le ?_ ?_, hg.inO.mono_le ?_ ?_⟩
  all_goals intro p; apply Nat.pow_le_pow_right (by omega); omega

/-- On in-range requests the short preprocessing cost fits in the source block count. -/
theorem exists_clock (c d : ℕ) :
    ∃ K, ∀ p : ScheduleChallenge, 2 ≤ p.time → p.bit < paddedTime p.time + 1 →
      c * (((enc p).length + 1) ^ d + 1) + 8 ≤ K * (numBlocks p.time + 1) := by
  let P (u : ℕ) := c * ((4 * u + 8) ^ d + 1) + 8
  have hp : Cslib.PolynomiallyBounded P := by unfold P; fun_prop
  obtain ⟨A, D, hA⟩ := Cslib.polynomiallyBounded_iff_le.mp hp
  obtain ⟨B, hB⟩ := exists_size_pow_le_numBlocks D
  refine ⟨A * B, ?_⟩
  intro p ht hb
  have hbit := (Nat.size_le_size (hb.le.trans (paddedTime_add_one_le ht))).trans
    (Nat.size_mul_le 2 p.time)
  change p.bit.size ≤ 2 + p.time.size at hbit
  have htime := Nat.size_le_size (show p.time ≤ p.time + 2 by omega)
  have hlen : (enc p).length + 1 ≤ 4 * (p.time + 2).size + 8 := by rw [length_enc]; omega
  calc
    _ ≤ P (p.time + 2).size := by unfold P; gcongr
    _ ≤ _ := by rw [Nat.mul_assoc]; exact (hA _).trans (Nat.mul_le_mul_left _ (hB p.time))

end ScheduleChallenge
end Cslib.Complexity.CountingSimulation
