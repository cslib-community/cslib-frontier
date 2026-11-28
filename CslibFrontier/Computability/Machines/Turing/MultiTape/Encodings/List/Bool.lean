/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List

/-! # Length of the framed Boolean-list encoding

Each encoded Boolean occupies one bit. Framing each bit separately takes three bits per element.
-/

namespace Turing.MultiTapeTM

/-- The framed list representation of a Boolean word uses exactly three bits per element. -/
public theorem length_encList_encBool (word : List Bool) :
    (encList encBool word).length = 3 * word.length := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    simp only [encList_cons, List.length_append, length_frame, encBool_apply,
      List.length_nil, List.length_cons, ih]
    omega

end Turing.MultiTapeTM
