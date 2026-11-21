/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ResidueInverse
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits

/-!
# Checking a guessed residue against one operand query per path

After guessing every residue coefficient, the universal selector either checks a coefficient
or checks the locally computed inverse. The selector has room for the mandatory output branch
even when the coefficient count is already a power of two.
-/

@[expose] public section
namespace Cslib.Circuits.Frontier.FastContraction.ResidueInverse

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString Turing.MultiTapeATM
open Turing.MultiTapeATM.QuantifiedWord

/-- The degree bits are existentially guessed, followed by a universal challenge. -/
def flags (d : ℕ) : List Bool :=
  List.replicate d false ++ List.replicate (Nat.clog 2 (d + 1)) true

/-- A universal choice either tests a claimed operand bit or checks the inverse of the guess. -/
def dispatch (m i : ℕ) (claim : Bool) (guess : List Bool) (j : ℕ) : Bool ⊕ ℕ × Bool :=
  if decide (j < (modulus m).length) then .inr (j, guess.getD j false)
  else .inl (run ⟨m, i, guess⟩ == claim)

/-- Fields for the native terminal router. -/
structure Challenge where
  /-- Binary contraction scale. -/
  scale : ℕ
  /-- Binary output coefficient index. -/
  index : ℕ
  /-- Claimed bit of the residue inverse. -/
  claim : Bool
  /-- Guessed residue followed by the challenge in little-endian form. -/
  choices : List Bool

/-- The two indices are binary, and all choice bits are contiguous. -/
enc_structure encChallenge : Challenge where
  scale : encNat, index : encNat, claim : encBool, choices : encBits

/-- Unpack the guess and the universal selector from the actual terminal word. -/
def route (p : Challenge) : Bool ⊕ ℕ × Bool :=
  let d := (modulus p.scale).length
  dispatch p.scale p.index p.claim (p.choices.take d) (ofBits (p.choices.drop d))

/-- The degree can be charged in unary even though the ambient scale is binary. -/
theorem degree_polyTime :
    ComputableInPolyTime (fun m => (modulus m).length) encNat encUnary := by
  have h := unary_mul' (const 2) half_polyTime
  exact h.of_enc_eq fun m => by simp only [length_modulus]

/-- All flags are prepared in polynomial time in the binary scale. -/
theorem flags_polyTime :
    ComputableInPolyTime (fun m => flags (modulus m).length) encNat encBits := by
  have h := degree_polyTime
  have hs := binary_clog_two.comp (unary_to_binary.comp (unary_add' h (const 1)))
  exact ((bitsReplicate false).comp h).bitsAppend ((bitsReplicate true).comp hs)

/-- The terminal function charges only the guessed residue and the short metadata. -/
theorem computableInPolyTime_route :
    ComputableInPolyTime route encChallenge (encSum encBool (encPair encNat encBool)) := by
  have hm := encChallenge_scale_deg.computableInPolyTime
  have hi := encChallenge_index_deg.computableInPolyTime
  have hc := encChallenge_claim_deg.computableInPolyTime
  have hw := encChallenge_choices_deg.computableInPolyTime
  have hd := degree_polyTime.comp hm
  have hg := bitsTakeWithInput hw hd
  have hj := bitsToNat.comp (bitsDropWithInput hw hd)
  have hr := (sumInr encBool (encPair encNat encBool)).comp
    (hj.prod (listGetD_binary false hg hj))
  have hlocal := computableInPolyTime_run.comp (encInput_mk_polyTime hm hi hg)
  have hbit := decide_eq' hlocal hc
  unfold route dispatch
  simp only [Bool.beq_eq_decide_eq]
  exact ite' (binary_lt' hj (unary_to_binary.comp hd)) hr
    ((sumInl encBool (encPair encNat encBool)).comp hbit)

/-- Interpret a native result by either its verdict or one bit of the actual residue. -/
def answer (word : List Bool) : Bool ⊕ ℕ × Bool → Prop
  | .inl b => b = true
  | .inr (j, b) => word.getD j false = b

private theorem route_fields (m i : ℕ) (claim : Bool) (guess : List Bool)
    (hg : guess.length = (modulus m).length) (w j : ℕ) (hj : j < 2 ^ w) :
    route ⟨m, i, claim, guess ++ lowBits w j⟩ = dispatch m i claim guess j := by
  simp only [route, ← hg, List.take_left, List.drop_left, ofBits_eq_lsbValue, lsbValue_lowBits hj]

/-- A winning residue guess agrees everywhere with the actual input before the inverse check. -/
theorem plays_flags (m i : ℕ) (claim : Bool) (word : List Bool)
    (hw : word.length = (modulus m).length) :
    plays (fun choices => answer word (route ⟨m, i, claim, choices⟩)) []
      (flags (modulus m).length) ↔
      run ⟨m, i, word⟩ = claim := by
  let d := (modulus m).length
  let w := Nat.clog 2 (d + 1)
  let pred (g : List Bool) (j : ℕ) := answer word (dispatch m i claim g j)
  have he : d < 2 ^ w := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide) _)
  change plays _ [] (List.replicate d false ++ List.replicate w true) ↔ _
  rw [plays_exists_field]
  simp only [List.nil_append]
  have hinner (g : Fin (2 ^ d)) :
      plays (fun choices => answer word (route ⟨m, i, claim, choices⟩))
        (lowBits d g.val) (List.replicate w true) ↔
        ∀ j : Fin (2 ^ w), pred (lowBits d g.val) j.val := by
    rw [show List.replicate w true = List.replicate w true ++ [] by simp, plays_forall_field]
    simp only [plays, route_fields m i claim _ (length_lowBits d g.val) w _ (Fin.isLt _), pred]
  simp only [hinner]
  constructor
  · rintro ⟨g, hg⟩
    have hgword : lowBits d g.val = word := by
      apply List.ext_getElem (by simp [d, hw])
      intro j hj hwj
      have hjd : j < d := by simpa only [length_lowBits] using hj
      have h := hg ⟨j, hjd.trans he⟩
      have hjm : j < (modulus m).length := hjd
      simpa only [List.getD_eq_getElem _ _ hwj, List.getD_eq_getElem _ _ hj] using Eq.symm
          (show word.getD j false = (lowBits d g.val).getD j false by
            simpa only [pred, dispatch, hjm, decide_true, ↓reduceIte, answer] using h)
    have h := hg ⟨d, he⟩
    simpa [pred, dispatch, hgword, d, answer] using h
  · intro h
    have hfit : lsbValue word < 2 ^ d := by simpa only [hw, d] using lsbValue_lt word
    refine ⟨⟨lsbValue word, hfit⟩, ?_⟩
    intro j
    have hrecover : lowBits d (lsbValue word) = word := by
      simpa only [hw, d] using lowBits_lsbValue word
    dsimp [pred]
    rw [hrecover]
    by_cases hj : j.val < (modulus m).length <;> simp [dispatch, hj, answer, h]

end Cslib.Circuits.Frontier.FastContraction.ResidueInverse
