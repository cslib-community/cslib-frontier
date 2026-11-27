/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle

/-!
# Correctness of guessed oracle transcripts

Positive replies assert membership in the oracle, and negative replies assert non-membership.
Local instructions carry `false`. Together these conditions characterize the canonical
instruction-indexed transcript, independently of the complexity of the oracle language.
-/

public section
namespace Cslib.Complexity
variable {α : Type} {enc : α ↪ List Bool}

/-! ### Transcript certificates -/

section Transcript

open _root_.Turing _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeMachine

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]

/-- Every `true` bit of the transcript answers a pending query in `A`. -/
def oracleTranscriptYes (machine : MultiTapePTM k Bool Control Operation) (enc : α ↪ List Bool)
    (A : Set (List Bool)) : Set (α × List Bool) :=
  {x | ∀ i < x.2.length, x.2.getD i false = true →
    (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome ∧
      machine.pendingRequest (machine.replayPrefix (enc x.1) x.2 i) ∈ A}

/-- Every `false` bit of a pending query answers a query outside `A`. -/
def oracleTranscriptNo (machine : MultiTapePTM k Bool Control Operation) (enc : α ↪ List Bool)
    (A : Set (List Bool)) : Set (α × List Bool) :=
  {x | ∀ i < x.2.length, x.2.getD i false = false →
    (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome →
      machine.pendingRequest (machine.replayPrefix (enc x.1) x.2 i) ∉ A}

theorem mem_oracleTranscriptYes {machine : MultiTapePTM k Bool Control Operation}
    {A : Set (List Bool)} {x : α × List Bool} :
    x ∈ oracleTranscriptYes machine enc A ↔ ∀ i < x.2.length, x.2.getD i false = true →
      (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome ∧
        machine.pendingRequest (machine.replayPrefix (enc x.1) x.2 i) ∈ A :=
  Iff.rfl

theorem mem_oracleTranscriptNo {machine : MultiTapePTM k Bool Control Operation}
    {A : Set (List Bool)} {x : α × List Bool} :
    x ∈ oracleTranscriptNo machine enc A ↔ ∀ i < x.2.length, x.2.getD i false = false →
      (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome →
        machine.pendingRequest (machine.replayPrefix (enc x.1) x.2 i) ∉ A :=
  Iff.rfl

variable {machine : MultiTapePTM k Bool Control Operation} {A : Set (List Bool)}

open Classical in
/-- A transcript is certified by both `oracleTranscriptYes` and `oracleTranscriptNo` exactly when
it is the canonical transcript of oracle replies for `A` of its own length. -/
theorem mem_oracleTranscriptYes_inter_oracleTranscriptNo {x : α × List Bool} :
    x ∈ oracleTranscriptYes machine enc A ∩ oracleTranscriptNo machine enc A ↔
      x.2 = machine.oracleReplies (fun q => decide (q ∈ A)) x.2.length (enc x.1) := by
  rw [machine.eq_oracleReplies_iff]
  simp only [Set.mem_inter_iff, mem_oracleTranscriptYes, mem_oracleTranscriptNo]
  constructor
  · rintro ⟨hY, hN⟩ i hi
    cases hb : x.2.getD i false
    · cases hq : (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome
      · simp
      · simp [hN i hi hb hq]
    · obtain ⟨hq, hA⟩ := hY i hi hb
      simp [hq, hA]
  · intro h
    refine ⟨fun i hi hb => ?_, fun i hi hb hq => ?_⟩
    · rw [h i hi] at hb
      split_ifs at hb with hq
      · exact ⟨hq, of_decide_eq_true hb⟩
    · rw [h i hi] at hb
      simpa only [hq, ↓reduceIte, decide_eq_false_iff_not] using hb


end Transcript

end Cslib.Complexity
