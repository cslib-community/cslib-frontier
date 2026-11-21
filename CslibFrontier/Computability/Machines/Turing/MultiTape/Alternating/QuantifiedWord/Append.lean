/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields

/-!
# Concatenating physical quantified words

Later quantified checks may depend on the whole prefix chosen by earlier players. When the
prefix length is fixed, taking and dropping exactly that many bits reconstructs both phases.
-/

public section
namespace Turing.MultiTapeATM.QuantifiedWord

/-- Terminal equivalence is needed only at completions of exactly the advertised length. -/
theorem plays_congr_length (V W : List Bool → Prop) (pre flags : List Bool)
    (h : ∀ xs, xs.length = flags.length → (V (pre ++ xs) ↔ W (pre ++ xs))) :
    plays V pre flags ↔ plays W pre flags := by
  induction flags generalizing pre with
  | nil => simpa only [List.append_nil, plays] using h [] rfl
  | cons p ps ih =>
    have hb (b : Bool) := ih (pre ++ [b]) fun xs hx => by
      simpa only [List.append_assoc, List.singleton_append] using h (b :: xs) (by simp [hx])
    cases p with
    | false => exact exists_congr hb
    | true => exact forall_congr' hb

private theorem plays_append (V : List Bool → Prop) (pre fs gs : List Bool) :
    plays V pre (fs ++ gs) ↔ plays (fun xs => plays V xs gs) pre fs := by
  induction fs generalizing pre with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | false => exact exists_congr fun b => ih (pre ++ [b])
    | true => exact forall_congr' fun b => ih (pre ++ [b])

/-- A common tape can hold two consecutive quantified games. A truth claim for the first
game's terminal is equivalent to running the second game on the already fixed first word. -/
theorem plays_split (V : List Bool → List Bool → Prop) (W : List Bool → Prop) (fs gs : List Bool)
    (h : ∀ xs : List Bool, xs.length = fs.length → (plays (V xs) [] gs ↔ W xs)) :
    plays (fun xs => V (xs.take fs.length) (xs.drop fs.length)) [] (fs ++ gs) ↔ plays W [] fs := by
  rw [plays_append]
  apply plays_congr_length
  intro xs hx
  simp only [List.nil_append]
  rw [← h xs hx]
  have he := plays_append_prefix (fun ys => V (ys.take fs.length) (ys.drop fs.length)) xs [] gs
  simp only [List.append_nil] at he
  apply he.trans
  apply plays_congr_length
  intro ys _
  simp only [List.nil_append, ← hx, List.take_left, List.drop_left]

/-- Unused choices preserve the terminal truth value, including when there are no flags. -/
theorem plays_constant (P : Prop) (pre flags : List Bool) : plays (fun _ => P) pre flags ↔ P := by
  induction flags generalizing pre with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [plays, ih]

end Turing.MultiTapeATM.QuantifiedWord
