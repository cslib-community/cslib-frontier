/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.IntegerVector.Normalize
meta import CslibFrontier.Algorithms.IntegerVector.Normalize

/-!
# Clients of rational integer-vector normalization

Check the common-denominator representation on zero, signed, and nonsquare-norm inputs,
and use the accuracy and native-runtime certificates through an ordinary module import.
-/

open Cslib.Algorithms.IntegerVector Turing.MultiTapeTM

set_option linter.hashCommand false

#guard normalize 128 [] = ⟨[], 1⟩
#guard normalize 128 [0, 0] = ⟨[0, 0], 1⟩
#guard normalize 128 [-3, 4] = ⟨[-384, 512], 641⟩
#guard normalize 128 [1, 1] = ⟨[128, 128], 182⟩
#guard normalize 0 [-3, 4] = ⟨[0, 0], 1⟩

example : ComputableInPolyTime (normalize 128) (encList encIntBin) encRationalVector :=
  computableInPolyTime_normalize (ComputableInPolyTime.const 128) ComputableInPolyTime.id'

example :
    ‖(normalize 128 (List.ofFn (fun _ : Fin 2 => (1 : ℤ)))).toEuclidean 2 -
      ‖WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ))‖⁻¹ •
        WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ))‖ ≤ 1 / 128 := by
  have hz : (WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ)) :
      EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    norm_num at hzero
  simpa only [Int.cast_one, Nat.cast_ofNat] using
    normalize_close 128 (by omega) (fun _ : Fin 2 => 1)
      (by simpa only [Int.cast_one] using hz)
