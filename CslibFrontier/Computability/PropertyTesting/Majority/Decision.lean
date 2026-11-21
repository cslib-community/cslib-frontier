/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.PropertyTesting.Majority
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# Binary arithmetic for the strict-majority tester

The decision after sampling in [Goldreich2007DraftR5, Exercise 10.9, p. 498] is computable
in time polynomial in the binary input length and binary sample count. For a fixed sample
budget, the count has bounded length. The input-addressing and fair-coin stages require
their own realization in the direct-access model of Definition 10.10.
-/

public section

namespace Cslib.BitString

open Turing.MultiTapeTM

/-- For fixed probe budget and tolerance, the comparison on the binary length and number of
sampled ones has a uniform deterministic polynomial-time realization. -/
theorem computableInPolyTime_majoritySampleAccepts (k : ℕ) (δ : ℚ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (majoritySampleAccepts p.1 k δ p.2))
      (encPair encNat encNat) encBool := by
  let input := encPair encNat encNat
  have hn := ComputableInPolyTime.fst encNat encNat
  have hs := ComputableInPolyTime.snd encNat encNat
  have hhalf : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 / 2) input encNat := by
    simpa only [Nat.shiftRight_eq_div_pow, Nat.pow_one] using
      ComputableInPolyTime.binary_shiftRight' hn (ComputableInPolyTime.const 1)
  have hwidth := ComputableInPolyTime.unary_succ.comp
    (ComputableInPolyTime.binary_log_two.comp hn)
  have hM := ComputableInPolyTime.binary_two_pow.comp hwidth
  have hleft := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.const (4 * δ.den * k))
    (ComputableInPolyTime.binary_add' hhalf (ComputableInPolyTime.const 1))
  have hright := ComputableInPolyTime.binary_mul' hM (ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const (4 * δ.den)) hs)
    (ComputableInPolyTime.const (δ.num.toNat * k)))
  exact ComputableInPolyTime.binary_le' hleft hright

end Cslib.BitString
