/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.ConvolutionOperand.Path
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! # Native routing for all signed terms of a reduced coefficient -/

@[expose] public section
namespace Cslib.ConvolutionOperand.Signed

open Turing.MultiTapeTM ComputableInPolyTime

/-- Parameters of a queried bit of the sparse trinomial product. -/
structure Query where
  /-- The middle exponent of the trinomial; its degree is twice this value. -/
  half : ℕ
  /-- Binary coefficient precision. -/
  precision : ℕ
  /-- Index of the output coefficient. -/
  index : ℕ
  /-- Two diagonal bits followed by row and shift bits. -/
  path : List Bool
  /-- Shifted partial-product bit. -/
  bit : ℕ
  /-- Select the carry component when true. -/
  carry : Bool
  /-- Select the right operand when true. -/
  right : Bool

/-- Path and binary numerical parameters of a signed operand query. -/
enc_structure encQuery : Query where
  half : encNat, precision : encNat, index : encNat, path : encBits, bit : encNat,
  carry : encBool, right : encBool

/-- Two leading digits select one of the three diagonals. A short path is padding. -/
def tag (path : List Bool) : ℕ :=
  if decide (2 ≤ path.length) then BitString.binaryValue (path.take 2) else 3

/-- The third diagonal exists only in the lower half of the coefficient array. -/
def live (p : Query) : Bool :=
  decide (tag p.path < 2) || (decide (tag p.path = 2) && decide (p.index < p.half))

/-- The convolution index specified by the two selector bits. -/
def diagonal (p : Query) : ℕ :=
  if decide (tag p.path = 0) then p.index
  else if decide (tag p.path = 1) then p.index + (if decide (p.index < p.half) then 2 * p.half
    else p.half)
  else p.index + 3 * p.half

/-- The remaining path enters the existing native row and shift router. -/
def ordinary (p : Query) : PathInput :=
  ⟨2 * p.half, p.precision, diagonal p, p.path.drop 2, p.bit, p.carry, p.right⟩

/-- Request a single operand coordinate or return zero padding. -/
def source (p : Query) : Option (ℕ × ℕ) :=
  if live p then run (unpack (ordinary p)) else none

/-- A requested signed operand coordinate lies within the coefficient array and precision. -/
theorem source_bounds {p : Query} {j i : ℕ} (h : source p = some (j, i)) :
    j < 2 * p.half ∧ i < p.precision := by
  unfold source at h
  split at h
  · simpa only [ordinary, unpack] using run_bounds h
  · simp at h

/-- Negative sum leaves complement their conjunction, and negative carry leaves supply one. -/
def correction (p : Query) : Bool := decide (tag p.path = 1) && (!p.carry || decide (p.bit = 0))

private theorem tag_polyTime : ComputableInPolyTime tag encBits encNat := by
  have hn := unary_to_binary.comp length_bits
  exact ite' (binary_le' (const 2) hn) (bitsBinaryValue.comp (bitsTakeWithInput id' (const 2)))
    (const 3)

/-- All physical signed operand addresses are computed on binary indices and one path. -/
theorem computableInPolyTime_source :
    ComputableInPolyTime source encQuery (encOption (encPair encNat encNat)) := by
  have hp := encQuery_path_deg.computableInPolyTime
  have ht := tag_polyTime.comp hp
  have hi := encQuery_index_deg.computableInPolyTime
  have hq := encQuery_half_deg.computableInPolyTime
  have hlo := binary_lt' hi hq
  have ha := bool_or.comp ((binary_lt' ht (const 2)).prod
    (bool_and.comp ((decide_eq' ht (const 2)).prod hlo)))
  have hd := binary_mul' (const 2) hq
  have hdiag := ite' (decide_eq' ht (const 0)) hi (ite' (decide_eq' ht (const 1))
    (binary_add' hi (ite' hlo hd hq)) (binary_add' hi (binary_mul' (const 3) hq)))
  exact ite' ha (computableInPolyTime_path.comp (encPathInput_mk_polyTime hd
    encQuery_precision_deg.computableInPolyTime hdiag (bitsDropWithInput hp (const 2))
    encQuery_bit_deg.computableInPolyTime encQuery_carry_deg.computableInPolyTime
    encQuery_right_deg.computableInPolyTime)) (const none)

/-- The sign correction is a local polynomial-time predicate on the same binary input. -/
theorem computableInPolyTime_correction : ComputableInPolyTime correction encQuery encBool :=
  bool_and.comp ((decide_eq' (tag_polyTime.comp encQuery_path_deg.computableInPolyTime)
    (const 1)).prod (bool_or.comp ((bool_not.comp encQuery_carry_deg.computableInPolyTime).prod
      (decide_eq' encQuery_bit_deg.computableInPolyTime (const 0)))))

end Cslib.ConvolutionOperand.Signed
