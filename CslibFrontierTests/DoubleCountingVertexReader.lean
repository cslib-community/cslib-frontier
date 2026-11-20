/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.VertexReader

/-!
# Ordinary-import fixed-width ID reader clients

The supplied word is the read-only choice source. These examples test actual query runs,
canonical codec agreement, missing bits, invalid IDs and the binary-state certificate.
-/

-- This module contains only checked clients.
set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingVertexReader

open Turing Turing.DoubleCounting.VertexReader Turing.MultiTapeTM

-- Two bits in MSB order give ID 2; no path or full branch is stored.
example : result ((machine 3).run [true, false] 2) = some 2 := by decide +kernel
example : result ((machine 3).run [false, true] 2) = some 1 := by
  rw [show 2 = Nat.size 3 by decide, result_eq_decodeVertex]
  decide +kernel

-- The accumulator can reach an invalid ID before the final range check rejects it.
example : ((machine 3).run [true, true] 1).value = 1 := by decide +kernel
example : ((machine 3).run [true, true] 2).value = 3 := by decide +kernel
example : result ((machine 3).run [true, true] 2) = none := by decide +kernel

-- A missing second bit marks truncation rather than supplying a guessed zero.
example : ((machine 3).run [true] 2).truncated = true := by decide +kernel
example : ((machine 3).run [true] 2).value = 1 := by decide +kernel
example : result ((machine 3).run [true] 2) = none := by decide +kernel
example : result ((machine 3).run [] 2) = none := by decide +kernel

-- The two reads are positions 0 and 1, then the routine halts and stays fixed.
example : (machine 3).query ((machine 3).run [true] 1) = 1 := by decide +kernel
example : (machine 3).halted ((machine 3).run [true] 1) = false := by decide +kernel
example : (machine 3).halted ((machine 3).run [true] 2) = true := by decide +kernel
example : (machine 3).run [true] 10 = (machine 3).run [true] 2 := by
  rw [run_eq_prefix, run_eq_prefix]
  rfl

-- This routine reads a prefix; suffix checking belongs to the enclosing scan codec.
example : result ((machine 3).run [false, true, true, true] 2) = some 1 := by decide +kernel
example : (machine 3).output [true, false] 2 = encOption encNat (some 2) := by
  rw [output_eq]
  decide +kernel

example : result ((machine 0).run [] 0) = none := by decide +kernel
example : result ((machine 1).run [false] 1) = some 0 := by decide +kernel
example : result ((machine 1).run [true] 1) = none := by decide +kernel

-- All-clock bounds apply equally to invalid and truncated choices.
example (w : List Bool) (t : ℕ) : ((machine 3).run w t).value < 4 := by
  have h := prefix_value_lt 3 w t
  have hm : min t (Nat.size 3) ≤ 2 := (Nat.min_le_right t (Nat.size 3)).trans_eq (by decide)
  have hp : 2 ^ min t (Nat.size 3) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hm
  exact h.trans_le hp

example (w : List Bool) (t : ℕ) : (encState ((machine 3).run w t)).length ≤ 21 := by
  have h := length_run_le 3 w t
  convert h using 1
  decide +kernel

-- An ordinary client can consume the actual native space certificate.
example : ∃ time c, ComputableInTimeAndSpace
    (fun w : List Bool =>
      (Cslib.DoubleCounting.Scan.Binary.decodeVertex (N := 3) (w.take 2)).map Fin.val)
    encBits (encOption encNat) time (fun w => c * (Nat.log2 w.length + 3)) := by
  simpa [show Nat.size 3 = 2 by decide, Nat.add_comm, Nat.add_left_comm] using native_decoder 3

end CslibFrontierTests.DoubleCountingVertexReader
