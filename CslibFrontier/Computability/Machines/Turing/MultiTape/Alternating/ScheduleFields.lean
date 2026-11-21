/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingPrepare
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ScheduleHeightInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OPrimitives

/-!
# Preparing a power-of-two schedule tree from its half-length

The initializer's short parameter record stores the binary half-length of the raw schedule.
Two of its seven derived words have length linear in that half-length. Both are computed
with a linear output charge plus a polynomial in the short parameter record.
-/

public section

namespace Turing.MultiTapeATM.ScheduleFields

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query
open CarryLookaheadCountingInitialLayout

/-- The count evaluated on a schedule of length twice the stored half-length. -/
@[expose] def expanded (a : CountingInput.Input) : CountingInput.Input :=
  ⟨2 ^ (2 * a.count), a.query⟩

/-- The initializer installs five query fields and the binary and unary tree heights. -/
inductive Field
  | stored (field : CountingInput.Field)
  | height
  | unary

/-- The exact word installed on a selected tape of the evaluator. -/
@[expose] def word : Field → CountingInput.Input → List Bool
  | .stored .count, a => encNat (2 ^ (2 * a.count))
  | .stored f, a => CountingInput.word f a
  | .height, a => encNat (2 * a.count)
  | .unary, a => encUnary (2 * a.count)

/-- Common form of the field clocks; only the short source is raised to a power. -/
@[expose] def budget (d : ℕ) (a : CountingInput.Input) : ℕ :=
  ((CountingInput.encInput a).length + 1) ^ d + a.count

private theorem short {f : CountingInput.Input → List Bool}
    (hf : ComputableInPolyTime f CountingInput.encInput encBits) :
    ∃ d, ComputableInO f CountingInput.encInput encBits (budget d) (budget d) := by
  obtain ⟨d, e, h⟩ := hf.exists_degree
  exact ⟨d, h.inO.mono_le (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _)⟩

private theorem count_polyTime :
    ComputableInPolyTime CountingInput.Input.count CountingInput.encInput encNat :=
  (CountingInput.word_polyTime .count).of_enc_eq fun _ => rfl

private theorem long {f : ℕ → List Bool}
    (hf : ComputableInO f ScheduleHeightWord.encHalf encBits id id) :
    ∃ d, ComputableInO (fun a : CountingInput.Input => f a.count) CountingInput.encInput
      encBits (budget d) (budget d) := by
  have hp : ComputableInPolyTime (fun a : CountingInput.Input => (false, a.count))
      CountingInput.encInput (encPair encBool encNat) :=
    (ComputableInPolyTime.const false).prod count_polyTime
  obtain ⟨d, e, h⟩ := hp.exists_degree
  have hc : ComputableInO (fun a : CountingInput.Input => a.count) CountingInput.encInput
      ScheduleHeightWord.encHalf _ _ := h.inO.of_enc_eq fun _ => rfl
  exact ⟨d, hf.comp hc⟩

/-- Each field has a native machine with the stated additive long-word charge. -/
theorem computable_word (f : Field) :
    ∃ d, ComputableInO (word f) CountingInput.encInput encBits (budget d) (budget d) := by
  cases f with
  | stored f =>
    cases f with
    | count => exact long ScheduleHeightWord.leafCount_inO
    | width => exact short (CountingInput.word_polyTime .width)
    | metadata => exact short (CountingInput.word_polyTime .metadata)
    | header => exact short (CountingInput.word_polyTime .header)
    | status => exact short (CountingInput.word_polyTime .status)
  | unary => exact long ScheduleHeightWord.unary_inO
  | height =>
    have enc : ComputableInPolyTime (fun n : ℕ => encNat n) encNat encBits := .of_eq fun _ => rfl
    apply short
    exact enc.comp (show ComputableInPolyTime (fun a : CountingInput.Input => 2 * a.count)
      CountingInput.encInput encNat from
        ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) count_polyTime)

/-- The evaluator tape that holds a selected field. -/
@[expose] def slot (k r q : ℕ) : Field → Fin (CarryLookaheadCountingLayout.size k r q)
  | .stored f => destination k r q f
  | .height => CarryLookaheadCountingInitialLayout.height k r q
  | .unary => CarryLookaheadCountingInitialLayout.unary k r q

/-- Read a selected field of an intermediate layout. -/
@[expose] def get (fields : Fields) : Field → List Bool
  | .stored f => fields.get f
  | .height => fields.height
  | .unary => fields.unary

/-- Install a selected word in the semantic description of the evaluator tapes. -/
@[expose] def set (fields : Fields) : Field → List Bool → Fields
  | .stored f, w => fields.set f w
  | .height, w => { fields with height := w }
  | .unary, w => { fields with unary := w }

theorem words_slot (k r q : ℕ) (context : List Bool) (fields : Fields) (f : Field) :
    words k r q context fields (slot k r q f) = get fields f := by
  cases f <;> simp [slot, get]

theorem words_set (k r q : ℕ) (context : List Bool) (fields : Fields) (f : Field)
    (w : List Bool) :
    Function.update (words k r q context fields) (slot k r q f) w =
      words k r q context (set fields f w) := by
  cases f with
  | stored h => exact words_update_field k r q context fields h w
  | height => exact words_update_height k r q context fields w
  | unary => exact words_update_unary k r q context fields w

end Turing.MultiTapeATM.ScheduleFields
