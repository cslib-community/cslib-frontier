/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.InterpolationGrid
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Native bit access to interpolation-grid factors

The denominator and numerator leaves need only the indices of two standard zero-one points
and the requested coefficient and bit. Every index is supplied in binary. The bit lookup
caps its unary working index at the binary length of the corresponding point number.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.InterpolationGrid

open Turing.MultiTapeTM ComputableInPolyTime

/-- One query to the numerator and denominator leaves of a Lagrange basis polynomial. -/
structure Input where
  points : ℕ
  center : ℕ
  index : ℕ
  degree : ℕ
  coordinate : ℕ
  bit : ℕ

/-- All six public fields are binary, including the two independent coefficient indices. -/
enc_structure encInput : Input where points : encNat, center : encNat, index : encNat,
  degree : encNat, coordinate : encNat, bit : encNat

/-- Both leaf bits, using the common grid point and center. -/
@[expose] def run (x : Input) : Bool × Bool :=
  (factorBit x.points x.center x.index x.coordinate x.bit,
    linearBit x.points x.center x.index x.degree x.coordinate x.bit)

private theorem bitAt {α : Type} {enc : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat) (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun x => (n x).testBit (i x)) enc encBool := by
  have h := binary_testBit hn (binary_min_unary' (binary_size.comp hn) hi)
  exact h.of_enc_eq fun x => by
    by_cases hle : i x ≤ (n x).size
    · simp [Nat.min_eq_right hle]
    · have high := Nat.lt_size_self (n x)
      have hs := Nat.le_of_not_ge hle
      simp [Nat.min_eq_left hs, Nat.testBit_lt_two_pow high,
        Nat.testBit_lt_two_pow (high.trans_le (Nat.pow_le_pow_right two_pos hs))]

/-- Both bits have one polynomial-time multitape certificate in the actual binary input size. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput (encPair encBool encBool) := by
  have hn := encInput_points_deg.computableInPolyTime
  have hi := encInput_center_deg.computableInPolyTime
  have hj := encInput_index_deg.computableInPolyTime
  have hk := encInput_degree_deg.computableInPolyTime
  have hr := encInput_coordinate_deg.computableInPolyTime
  have hb := encInput_bit_deg.computableInPolyTime
  have h₀ := decide_eq' hb (const 0)
  have hz := ComputableInPolyTime.decide_and (decide_eq' hr (const 0)) h₀
  have hleft := bitAt hi hr
  have hright := bitAt hj hr
  have hactive := ComputableInPolyTime.decide_and (binary_lt' hj hn) (decide_ne hj hi)
  have hden := ite_decide hactive (ite hleft
    (bool_and.comp ((bool_not.comp hright).prod h₀)) hright) hz
  have linear (k : ℕ) := ComputableInPolyTime.decide_and (decide_eq' hk (const k)) hz
  have hnum := ite_decide hactive (ite_decide (decide_eq' hk (const 0)) hright (linear 1))
    (linear 0)
  exact hden.prod hnum

end Cslib.Circuits.Frontier.FastContraction.InterpolationGrid
