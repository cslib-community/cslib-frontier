/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-!
# Decoding prefixes of framed lists

A complete prefix of a framed list decodes to the corresponding elements even if the copied
word ends inside a later frame.
-/

public section

namespace Turing.MultiTapeTM

open Cslib

/-- Complete framed list elements remain the initial frames after appending any raw suffix. -/
theorem frames_encList_append {α : Type*} (enc : α ↪ List Bool)
    (values : List α) (suffix : List Bool) :
    frames (encList enc values ++ suffix) = values.map enc ++ frames suffix := by
  induction values with
  | nil => simp only [encList_nil, List.nil_append, List.map_nil]
  | cons value values ih =>
    rw [encList_cons, List.append_assoc, frames_frame_append, ih, List.map_cons,
      List.cons_append]

/-- If the copied bits contain the encodings of the first `count` elements, these elements
decode correctly regardless of the contents or completeness of the remaining frames. -/
theorem Decoder.list_decode_take {α : Type} {enc : α ↪ List Bool} (decoder : Decoder enc)
    (values : List α) (count bits : ℕ) (hfit : (encList enc (values.take count)).length ≤ bits) :
    ((decoder.list).decode ((encList enc values).take bits)).take count = values.take count := by
  by_cases hshort : values.length ≤ count
  · rw [List.take_of_length_le hshort] at hfit ⊢
    rw [List.take_of_length_le hfit, decoder.list.decode_enc, List.take_of_length_le hshort]
  · have hlength : (values.take count).length = count := by simp [List.length_take]; omega
    have henc : encList enc values =
        encList enc (values.take count) ++ encList enc (values.drop count) := by
      rw [← encList_append, List.take_append_drop]
    change ((frames ((encList enc values).take bits)).map decoder.decode).take count = _
    rw [henc, List.take_append, List.take_of_length_le hfit, frames_encList_append,
      List.map_append, List.map_map, show decoder.decode ∘ enc = id from funext decoder.decode_enc,
      List.map_id]
    simpa only [hlength] using List.take_append_length (l₁ := values.take count)
      (l₂ := (frames ((encList enc (values.drop count)).take
        (bits - (encList enc (values.take count)).length))).map decoder.decode)

end Turing.MultiTapeTM
