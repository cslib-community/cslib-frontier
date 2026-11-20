/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.Combined

/-! # Ordinary-import clients of combined-input parameter/ID dispatch -/

-- This module contains only checked clients.
set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingCombined
open Turing Turing.MultiTapeTM Turing.DoubleCounting
open Combined

-- The existing parameter prefix is framed once; the canonical MSB ID word is unchanged.
example : encInput ⟨⟨3, 2⟩, [true, false]⟩ =
    frame (VertexParameters.encParameters ⟨3, 2⟩) ++ [true, false] := rfl
example : (start ⟨⟨3, 2⟩, []⟩).skip = 15 := by decide +kernel

-- Public step computation needs no public feed helper.
example : step (⟨0, ⟨3, 2, 0, 0, false⟩⟩, true) =
    ⟨0, ⟨3, 2, 1, 1, false⟩⟩ := rfl
example : step (⟨0, ⟨3, 2, 2, 1, false⟩⟩, true) =
    ⟨0, ⟨3, 2, 2, 1, false⟩⟩ := rfl
example : step (⟨1, ⟨3, 2, 0, 0, false⟩⟩, true) =
    ⟨0, ⟨3, 2, 0, 0, false⟩⟩ := rfl

example : run ⟨⟨3, 2⟩, [true, false]⟩ = some 2 := by decide +kernel
example : run ⟨⟨3, 2⟩, [true, true]⟩ = none := by decide +kernel
example : run ⟨⟨3, 2⟩, [false]⟩ = none := by decide +kernel
example : run ⟨⟨3, 2⟩, []⟩ = none := by decide +kernel
example : run ⟨⟨3, 1000000⟩, [false, false]⟩ = none := by decide +kernel
example : run ⟨⟨0, 0⟩, []⟩ = none := by decide +kernel
example : run ⟨⟨1, 1⟩, [false]⟩ = some 0 := by decide +kernel
example : run ⟨⟨1, 1⟩, [true]⟩ = none := by decide +kernel
example : run ⟨⟨4, 3⟩, [false, true, true]⟩ = some 3 := by decide +kernel
example : run ⟨⟨4, 2⟩, [true, true]⟩ = none := by decide +kernel

-- A supplied suffix is traversed without changing the one-ID result.
example : run ⟨⟨3, 2⟩, [false, true, true, true, false]⟩ = some 1 := by decide +kernel

-- Dispatch context is charged at any prefix, independently of the suffix length.
example (w : List Bool) (j : ℕ) :
    (encContext ((encInput ⟨⟨3, 2⟩, w⟩ |>.take j).foldl
      (fun s b => step (s, b)) (start ⟨⟨3, 2⟩, w⟩))).length ≤ 96 := by
  have h := prefix_length_le (⟨⟨3, 2⟩, w⟩ : Input) j
  convert h using 1
  change 96 = 12 * ((VertexParameters.encParameters ⟨3, 2⟩).length + 1)
  decide +kernel

-- The native witness computes the validated prior-reader specification, uniformly in N.
example : ∃ time c, ComputableInTimeAndSpace
    (fun x : Input => (VertexParameters.prepare x.parameters).bind (fun s =>
      VertexReader.result ((VertexReader.machine 0).runFrom x.choices s x.parameters.width)))
    encInput (encOption encNat) time
    (fun x => c * ((VertexParameters.encParameters x.parameters).length + 1)) := by
  have he : (fun x : Input => (VertexParameters.prepare x.parameters).bind (fun s =>
      VertexReader.result
        ((VertexReader.machine 0).runFrom x.choices s x.parameters.width))) = run :=
    funext fun x => (run_eq x).symm
  rw [he]
  exact native_run

end CslibFrontierTests.DoubleCountingCombined
