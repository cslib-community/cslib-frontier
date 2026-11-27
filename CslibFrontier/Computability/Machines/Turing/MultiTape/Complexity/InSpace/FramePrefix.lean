/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.FrameMachines
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# Native extraction of an encoded framed header

A layout equality `encIn x = frame (encOut (f x)) ++ suffix x` identifies the first framed
field of an input. `ComputableInTimeAndSpace.framedPrefix` realizes that field projection using
the existing zero-work-tape frame transducer. Its time bound is twice the complete input length
plus three, and its workspace is zero. The suffix can be arbitrarily long.

`ComputableInSpace.framedPrefix` supplies the corresponding compositional space certificate,
charging only the extracted header's encoding. This additional charge accounts for retaining the
output in a later computation; it is not a charge for the suffix. These certificates concern
inputs in the supplied encoding's image, not arbitrary malformed framed words.

This original shared certificate supports runtime parameter and controller-header extraction;
it does not initialize or execute a complete query machine.
-/

public section
namespace Turing.MultiTapeTM
open ComputableInSpace

/-- Extract the first framed encoded field with the existing native frame reader, without
work tapes. The layout premise leaves the remainder of the input unrestricted. -/
theorem ComputableInTimeAndSpace.framedPrefix {α β : Type*} (f : α → β)
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (suffix : α → List Bool)
    (layout : ∀ x, encIn x = frame (encOut (f x)) ++ suffix x) :
    ComputableInTimeAndSpace f encIn encOut
      (fun x => 2 * (encIn x).length + 3) (fun _ => 0) := by
  let tr := Internal.FrameMachines.readFrameT true
  refine ⟨0, _, inferInstance, tr.toTM, fun x => ?_⟩
  have he : tr.run tr.q₀ (encIn x) = encOut (f x) := by
    simp [tr, Internal.FrameMachines.readFrameT_run_true, layout x]
  rw [← he]
  exact tr.computesInTimeAndSpace_toTM _

/-- Extract a framed encoded field with a native space budget that charges its output alone,
independently of the length of the untouched suffix. -/
theorem ComputableInSpace.framedPrefix {α β : Type*} (f : α → β)
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (suffix : α → List Bool)
    (layout : ∀ x, encIn x = frame (encOut (f x)) ++ suffix x) :
    ComputableInSpace f encIn encOut (fun x => (encOut (f x)).length) := by
  exact ComputableInSpace.of_inO (ComputableInO.of_bounds (T := fun x => (encIn x).length)
    (ComputableInTimeAndSpace.framedPrefix f encIn encOut suffix layout) 3
    (fun _ => by omega) (fun _ => by omega) (fun _ => by omega))

/-- Compute the length of the framed header in the same space budget as its extraction.
For a framed prefix, this gives the binary offset of the original payload. -/
theorem ComputableInSpace.frameLength {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encHeader : β ↪ List Bool} {budget : α → ℕ}
    (h : ComputableInSpace f encIn encHeader budget) :
    ComputableInSpace (fun x => (frame (encHeader (f x))).length) encIn encNat budget := by
  have hword : ComputableInSpace (fun x => encHeader (f x)) encIn encBits budget :=
    h.of_enc_eq fun _ => (encBits_apply _).symm
  have hlength : ComputableInSpace List.length encBits encNat
      (fun w => (encBits w).length) :=
    (of_inO ComputableInO.lengthNat).weaken (.of_le fun w => by rw [encBits_apply])
  have hlen := budget_comp_linear hlength hword
  have hid : ComputableInSpace (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  have hoffset := budget_natSucc (budget_natAdd hid hid)
  exact (budget_comp_linear hoffset hlen).of_enc_eq fun _ => by
    simp only [length_frame, two_mul]

end Turing.MultiTapeTM
