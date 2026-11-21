/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointAnswer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives

/-!
# Reading tagged schedule endpoint answers

The endpoint scanner emits an explicit false tag for each absent option. The standard nested
option encoding omits that false tag. The following finite transducer examines the first two
positions and copies every subsequent binary digit verbatim, including false digits.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointAnswer

private def standard : Transducer Bool State where
  q₀ := .validity
  step q b := match q with
    | .validity => (.found, if b then [true] else [])
    | .found => (.copy, if b then [true] else [])
    | .copy => (.copy, [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> decide
  length_final_le _ := by decide

private theorem run_copy (bits : List Bool) : standard.run .copy bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    change b :: standard.run .copy bits = b :: bits
    rw [ih]

/-- Convert the actual emitted validity/found tags into standard nested options in linear time. -/
theorem computableInDegree_standard : ComputableInDegree (id : Option (Option ℕ) → _)
    encAnswer (encOption (encOption encNat)) 1 1 := by
  apply ComputableInDegree.of_transducer standard
  rintro (_ | (_ | n))
  · rfl
  · rfl
  · change true :: true :: encNat n = true :: true :: standard.run .copy (encNat n)
    rw [run_copy]

end Turing.MultiTapeTM.ScheduleEndpointAnswer
