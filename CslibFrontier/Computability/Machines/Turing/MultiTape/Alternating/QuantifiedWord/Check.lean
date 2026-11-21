/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import Mathlib.Data.List.GetD

/-! # Checking any Boolean operation with one operand request per play -/

@[expose] public section
namespace Turing.MultiTapeATM.QuantifiedWord.Check

open Cslib.BitString Turing.MultiTapeTM

/-- Guess the complete input and universally select an operand or the operation itself. -/
def flags (d : ℕ) : List Bool :=
  List.replicate d false ++ List.replicate (Nat.clog 2 (d + 1)) true

/-- A padding index checks the guessed operation, including the mandatory index `d`. -/
def dispatch (d : ℕ) (test : List Bool → Bool) (guess : List Bool) (j : ℕ) :
    Bool ⊕ ℕ × Bool :=
  if decide (j < d) then .inr (j, guess.getD j false) else .inl (test guess)

/-- Decode one completed play into a local verdict or an addressed bit. -/
def route (d : ℕ) (test : List Bool → Bool) (s : List Bool) : Bool ⊕ ℕ × Bool :=
  dispatch d test (s.take d) (ofBits (s.drop d))

/-- The single external operand against which a completed play is checked. -/
def answer (word : List Bool) : Bool ⊕ ℕ × Bool → Prop
  | .inl b => b = true
  | .inr (j, b) => word.getD j false = b

private theorem fields (d : ℕ) (test : List Bool → Bool) (guess : List Bool)
    (hg : guess.length = d) (w j : ℕ) (hj : j < 2 ^ w) :
    route d test (guess ++ lowBits w j) = dispatch d test guess j := by
  simp only [route, ← hg, List.take_left, List.drop_left, ofBits_eq_lsbValue, lsbValue_lowBits hj]

/-- The game verifies exactly the operation on the true input, for every arity including zero. -/
theorem plays_flags (d : ℕ) (test : List Bool → Bool) (word : List Bool) (hw : word.length = d) :
    plays (fun s => answer word (route d test s)) [] (flags d) ↔ test word = true := by
  let w := Nat.clog 2 (d + 1)
  let pred (g : List Bool) (j : ℕ) := answer word (dispatch d test g j)
  have he : d < 2 ^ w := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide) _)
  change plays _ [] (List.replicate d false ++ List.replicate w true) ↔ _
  rw [plays_exists_field]
  simp only [List.nil_append]
  have hinner (g : Fin (2 ^ d)) :
      plays (fun s => answer word (route d test s)) (lowBits d g.val)
        (List.replicate w true) ↔ ∀ j : Fin (2 ^ w), pred (lowBits d g.val) j.val := by
    rw [show List.replicate w true = List.replicate w true ++ [] by simp, plays_forall_field]
    simp only [plays, fields d test _ (length_lowBits d g.val) w _ (Fin.isLt _), pred]
  simp only [hinner]
  constructor
  · rintro ⟨g, hg⟩
    have hgword : lowBits d g.val = word := by
      apply List.ext_getElem (by simp [hw])
      intro j hj hwj
      have hjd : j < d := by simpa only [length_lowBits] using hj
      have h := hg ⟨j, hjd.trans he⟩
      simpa only [List.getD_eq_getElem _ _ hwj, List.getD_eq_getElem _ _ hj] using Eq.symm
          (show word.getD j false = (lowBits d g.val).getD j false by
            simpa only [pred, dispatch, hjd, decide_true, ↓reduceIte, answer] using h)
    have h := hg ⟨d, he⟩
    simpa [pred, dispatch, hgword, answer] using h
  · intro h
    have hfit : lsbValue word < 2 ^ d := by simpa only [hw] using lsbValue_lt word
    refine ⟨⟨lsbValue word, hfit⟩, ?_⟩
    intro j
    have hrecover : lowBits d (lsbValue word) = word := by
      simpa only [hw] using lowBits_lsbValue word
    dsimp [pred]
    rw [hrecover]
    by_cases hj : j.val < d <;> simp [dispatch, hj, answer, h]

end Turing.MultiTapeATM.QuantifiedWord.Check
