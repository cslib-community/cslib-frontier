/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleValidationNative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Mathlib.Data.Nat.Size

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# Linear preparation of root endpoint addresses

The input carries the raw schedule and two binary indices. The preparer validates the schedule
and counts its bits in binary. Halving that count drops its least significant bit. On invalid
schedules it supplies zero movement pairs, so the classifier rejects every edge. The classifier
therefore receives only the two binary indices and a logarithmic-size count.
-/

public section

namespace Turing.MultiTapeTM.RootEndpointInput

open RootEndpointQuery (Input)

/-- Framed raw movements, framed binary copy count, and the binary half-edge index. -/
enc_structure encInput : Input where raw : encBits, copies : encNat, edge : encNat

/-- External input length including both frames. -/
theorem length_encInput (a : Input) :
    (encInput a).length = 2 * a.raw.length + 2 * a.copies.bits.length + a.edge.bits.length + 2 := by
  simp [encInput_apply, encInputFields, encPair_apply, encNat_apply]
  omega

/-- Size parameter for arithmetic on the schedule length and the two supplied indices. -/
@[expose] def shortSize (a : Input) : ℕ :=
  a.raw.length.size + a.copies.size + a.edge.size + 1

/-- Prepare the binary pair count and both indices. A malformed schedule has no admitted edges. -/
@[expose] def addressInput (k : ℕ) (a : Input) : RootEndpointAddress.Input :=
  ⟨if ScheduleBits.validate k a.raw then a.raw.length / 2 else 0, a.copies, a.edge⟩

/-- The prepared movement-pair count is bounded by the raw bit count, on all inputs. -/
theorem addressInput_pairs_le (k : ℕ) (a : Input) : (addressInput k a).pairs ≤ a.raw.length := by
  unfold addressInput
  split_ifs <;> simp [Nat.div_le_self]

/-- Binary address length charges only the bit length of the schedule length. -/
theorem length_addressInput_le (k : ℕ) (a : Input) :
    (RootEndpointAddress.encInput (addressInput k a)).length ≤ 2 * shortSize a := by
  have hp := Nat.size_le_size (addressInput_pairs_le k a)
  rw [RootEndpointAddress.length_encInput]
  simp only [Nat.size_eq_bits_len]
  change 2 * (addressInput k a).pairs.size + 2 * a.copies.size + a.edge.size + 2 ≤ 2 * shortSize a
  unfold shortSize
  omega

/-- The zero-pair substitution implements the original validation guard before resolution. -/
theorem query_eq_addressInput (k : ℕ) (a : Input) :
    RootEndpointQuery.query k a =
      (RootEndpointAddress.query k (addressInput k a)).bind
        (RootEndpointQuery.resolve k a.raw) := by
  rw [RootEndpointQuery.query_eq_address]
  cases hv : ScheduleBits.validate k a.raw with
  | true => simp [addressInput, RootEndpointQuery.addressInput, hv]
  | false =>
    simp [addressInput, RootEndpointAddress.query,
      RootEndpointAddress.edgeCount, RootEndpointAddress.intervals, hv]

/-- One machine validates the raw table and prepares the short classifier input in time and
workspace linear in the full external input length. -/
theorem addressInput_deg (k : ℕ) :
    ComputableInDegree (addressInput k) encInput RootEndpointAddress.encInput 1 1 := by
  have hv : ComputableInDegree (ScheduleBits.validate k) encBits encBool 1 1 :=
    .of_transducer (ScheduleValidation.reader k) fun w =>
      (ScheduleValidation.run_eq_validate k w).symm
  have hl : ComputableInDegree List.length encBits encNat 1 1 :=
    ComputableInO.lengthNat.computableInDegree DegreeBounded.self DegreeBounded.self le_rfl
  have ht : ComputableInDegree List.tail encBits encBits 1 1 :=
    ListEncoding.tail (enc₁ := encBool) (enc := encBits)
  have hh : ComputableInDegree (fun n : ℕ => n / 2) encNat encNat 1 1 :=
    (ht.of_encIn_eq (encIn' := encNat) Nat.bits fun _ => rfl).of_enc_eq
      fun n => Nat.div2_bits_eq_tail n
  have hp : ComputableInDegree
      (fun w : List Bool => if ScheduleBits.validate k w then w.length / 2 else 0)
      encBits encNat 1 1 :=
    hv.ite_le (f := fun w => w.length / 2) (g := fun _ => 0)
      (hh.comp (g := List.length) hl) (.const 0) (by decide) (by decide)
  exact RootEndpointAddress.encInput_mk_deg.comp
    ((hp.comp encInput_raw_deg).prod (encInput_copies_deg.prod encInput_edge_deg))

end Turing.MultiTapeTM.RootEndpointInput
