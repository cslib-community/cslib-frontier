/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit

/-! Ordinary charged-space clients: constant outputs at zero budget, independent workspace
composition, and binary digit access. Zero budget means constant space, not zero actual cells. -/

open Turing.MultiTapeTM

assert_not_exists Turing.MultiTapeTM.ComputableTidilyInSpace
assert_not_exists Turing.MultiTapeTM.ComputableInSpace.tidy
assert_not_exists Turing.MultiTapeTM.ComputableInSpace.of_tidy

-- A nonempty, ordered output remains legal at zero budget on unbounded inputs.
example : ComputableInSpace (fun _ : List Bool => ([true, false], [false, true]))
    encBits (encPair encBits encBits) (fun _ => 0) := by
  simpa using (ComputableInSpace.constZero (encIn := encBits) (encB := encBits)
    [true, false]).prod (ComputableInSpace.constZero (encIn := encBits) (encB := encBits)
    [false, true])

-- No relation between the two workspace envelopes, or their existential clocks, is assumed.
example {f g : List Bool → List Bool} {S W : List Bool → ℕ}
    (hf : ComputableInSpace f encBits encBits S)
    (hg : ComputableInSpace g encBits encBits W) :
    ComputableInSpace (fun x => g (f x)) encBits encBits (fun x => S x + W (f x)) ∧
    (fun x => (encBits (g (f x))).length) ≼ (fun x => S x + W (f x)) := by
  have h := hg.comp hf
  exact ⟨h, h.length_le⟩

-- An arbitrary-length identity cannot be charged to constant space.
example : ¬ComputableInSpace (id : List Bool → List Bool) encBits encBits (fun _ => 0) := by
  rintro ⟨t, c, -, hl⟩
  simpa [encBits] using hl (List.replicate (c + 1) true)

-- Use the actual binary reader after two ordinary projections and a conditional.
example : ComputableInSpace
    (fun q : ℕ × ℕ => if q.1.testBit q.2 then [true, false] else [false, true])
    (encPair encNat encNat) encBits
    (fun q => 32 * ((encPair encNat encNat q).length + 1)) := by
  simpa using ComputableInSpace.natTestBit.ite
    (ComputableInSpace.constZero [true, false])
    (ComputableInSpace.constZero [false, true])
