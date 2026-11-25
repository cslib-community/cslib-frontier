/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module

import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixFreePair

/-!
# Tests for common block extension on word queries

Exercise a proper-prefix pair at width two, with the longer query first, and check
that the flat batch search agrees with block search for repeated and exhausted blocks.
-/

open Cslib.Crypto.PRF

example : separatingWordBlock 2 [true, false, false, false] [true, false] = [true, true] := by
  decide

example :
    let u := [true, false, false, false]
    let v := [true, false]
    let c := separatingWordBlock 2 u v
    (¬ u ++ c <+: v ++ c) ∧ (¬ v ++ c <+: u ++ c) :=
  separatingWordBlock_prefix_incomparable (by decide) (by decide) (by decide) (by decide)

example : freshBatchWordBlock 1 [[false], [false, false]] = some [true] := by
  rw [freshBatchWordBlock_eq_map_freshBatchBlock]
  decide

example : freshBatchWordBlock 1 [[false], [true]] = none := by
  rw [freshBatchWordBlock_eq_map_freshBatchBlock]
  decide
