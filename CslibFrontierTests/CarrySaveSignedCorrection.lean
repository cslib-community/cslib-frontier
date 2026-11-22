/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveSignedCorrection

namespace CslibFrontierTests.CarrySaveSignedCorrection

open Polynomial Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib.ConvolutionOperand.Signed Cslib.Circuits.Frontier.FastContraction

-- A padded zero index still contributes the negative diagonal's carry correction.
example : rawCorrection ⟨[true], [false, true], [true], [false, true], true,
    [false, false]⟩ = true := by decide

-- Changing only the low bit disables that carry correction.
example : rawCorrection ⟨[true], [false, true], [true], [false, true], true,
    [true, false]⟩ = false := by decide

-- A one-bit path is padding, even when the queried index is zero.
example : rawCorrection ⟨[true], [false, true], [true], [false], true,
    [false, false]⟩ = false := by decide

-- One native family handles the padded-index and short-path boundaries on real leaf storage.
-- Both claims and carry selectors are tested, with no restriction on the four persistent words.
example : ∃ (k : ℕ) (Q : Type) (_ : Finite Q)
    (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool Q) (C d : ℕ),
    ∀ (input context count width : List Bool) (shortPath bit carry claim : Bool),
    let path := if shortPath then [false] else [false, true]
    let time := C * (context.length + count.length + width.length + (4 + 2) ^ d + 1)
    let cfg := (CarrySaveLeaf.initial k input context count width [] [bit, false] path []
      0 false).withState (some (leaf carry claim).toPTM.initial)
    (leaf carry claim).HaltsWithin time cfg ∧
      ((leaf carry claim).AcceptsWithin time cfg ↔
        (!shortPath && (!carry || !bit)) = claim) := by
  obtain ⟨k, Q, hQ, leaf, C, d, h⟩ :=
    Turing.MultiTapeATM.CarrySaveSignedCorrection.exists_leaves
  refine ⟨k, Q, hQ, leaf, C, d, fun input context count width shortPath bit carry claim => ?_⟩
  let path := if shortPath then [false] else [false, true]
  have hfront : CarrySaveStream.Frontier [] 0 0 := by
    intro j
    simp
  have hsize : ([] : List Bool).length + [bit, false].length + path.length ≤ 4 := by
    cases shortPath <;> simp [path]
  have hbit : Cslib.BitString.lsbValue [bit, false] < 2 := by
    cases bit <;> decide
  obtain ⟨hh, ha⟩ := h input context count width 4
  have hv : Cslib.Circuits.Boolean.CarrySaveQuery.value
      (signedPorts (0 : (ZMod (2 ^ 2))[X]) 0 1 0 2)
      ⟨path, 0, carry, Cslib.BitString.lsbValue [bit, false]⟩ =
        (!shortPath && (!carry || !bit)) := by
    rw [value_port _ _ 1 0 2 path ⟨_, hbit⟩ carry]
    cases shortPath <;> cases bit <;> cases carry <;> rfl
  refine ⟨hh [] [bit, false] path [] 0 false carry claim hfront hsize, ?_⟩
  refine (ha (0 : (ZMod (2 ^ 2))[X]) 0 1 0 2 (by decide) (by decide)
    [] [bit, false] path [] 0 false carry claim hfront hsize hbit).trans ?_
  rw [hv]

end CslibFrontierTests.CarrySaveSignedCorrection
