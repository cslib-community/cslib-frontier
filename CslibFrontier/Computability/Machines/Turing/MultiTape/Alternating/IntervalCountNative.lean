/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.IntervalCountGame
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Uniform native parsing of the interval-sum certificate

Each chosen side appends one binary digit to the selected index. A valid subtotal can only
decrease. The remaining choice word shrinks, so iterating through all rounds has polynomial
cost in the binary count size and the actual choice word.
-/

public section

namespace Turing.MultiTapeATM.IntervalCountGame

open MultiTapeTM ComputableInPolyTime Cslib.BitString

/-- The challenged bit index is unary. Its length is at most the common field width for a real
descendant count challenge. The edge count itself is binary. -/
structure Input where
  count : ℕ
  bit : ℕ
  claim : Bool
  choices : List Bool

/-- Input for one native transfer from the completed count choices to its singleton. -/
enc_structure encInput : Input where count : encNat, bit : encUnary, claim : encBool,
  choices : encBits

private structure Cursor where
  rest : List Bool
  index : ℕ
  value : ℕ
  valid : Bool

private enc_structure encCursor : Cursor where rest : encBits, index : encNat, value : encNat,
  valid : encBool

private def advance (w : ℕ) (s : Cursor) : Cursor :=
  let left := ofBits (s.rest.take w)
  let rest := s.rest.drop w
  let side := rest.headD false
  if left ≤ s.value then
    ⟨rest.tail, s.index * 2 + (if side then 1 else 0), if side then s.value - left else left,
      s.valid⟩
  else { s with valid := false }

private def finish (s : Cursor) : Option (ℕ × ℕ) :=
  if s.valid then some (s.index, s.value) else none

private theorem finish_iterate (w h : ℕ) (s : Cursor) :
    finish ((advance w)^[h] s) =
      if s.valid then walk w h (s.index * 2 ^ h) s.value s.rest else none := by
  induction h generalizing s with
  | zero => simp [finish, walk]; rfl
  | succ h ih =>
    rw [Function.iterate_succ_apply, ih]
    by_cases hle : ofBits (s.rest.take w) ≤ s.value
    · cases hv : s.valid <;> cases hb : s.rest[w]?.getD false <;>
        simp [advance, walk, ← ofBits_eq_lsbValue, hle, hv, hb, Nat.add_mul, Nat.pow_succ,
          Nat.mul_assoc, Nat.mul_comm]
    · simp [advance, walk, ← ofBits_eq_lsbValue, hle]

private theorem advance_polyTime :
    ComputableInPolyTime (fun p : ℕ × Cursor => advance p.1 p.2)
      (encPair encUnary encCursor) encCursor := by
  let hw := fst encUnary encCursor
  let hs := snd encUnary encCursor
  have hr := encCursor_rest_polyTime hs
  have hi := encCursor_index_polyTime hs
  have hv := encCursor_value_polyTime hs
  have hok := encCursor_valid_polyTime hs
  have hl := bitsToNat.comp (bitsTakeWithInput hr hw)
  have hrest := bitsDropWithInput hr hw
  have hb := (ListEncoding.headD (enc₁ := encBool) (enc := encBits) false).computableInPolyTime.comp
    hrest
  exact ite_decide (binary_le' hl hv)
    (encCursor_mk_polyTime (bitsTail.comp hrest)
      (binary_add.comp ((binary_mul' hi (const 2)).prod (ite hb (const 1) (const 0))))
      (ite hb (binary_sub.comp (hv.prod hl)) hl) hok)
    (encCursor_mk_polyTime hr hi hv (const false))

private theorem growth (w : ℕ) (s : Cursor) :
    (encCursor (advance w s)).length ≤ (encCursor s).length + 12 := by
  unfold advance
  dsimp only
  split <;> rename_i hl
  · have h₁ := Nat.size_mul_le s.index 2
    have h₂ := Nat.size_add_le (s.index * 2) 1
    have h₃ := Nat.size_le_size (Nat.sub_le s.value (ofBits (s.rest.take w)))
    have h₄ := Nat.size_le_size hl
    have h₅ : (2 : ℕ).size = 2 := by decide
    have h₆ : (1 : ℕ).size = 1 := by decide
    cases (s.rest.drop w).headD false <;>
      simp [encCursor_apply, encCursorFields, encNat_apply, Nat.size_eq_bits_len] <;> omega
  · simp [encCursor_apply, encCursorFields]

/-- Parse an exact-total certificate without guessing another total. Width and height are
unary; the initial subtotal and selected index are binary. The initial interval starts at zero. -/
theorem computableInPolyTime_walk {α : Type} {enc : α ↪ List Bool}
    {w h value : α → ℕ} {choices : α → List Bool}
    (hw : ComputableInPolyTime w enc encUnary) (hh : ComputableInPolyTime h enc encUnary)
    (hv : ComputableInPolyTime value enc encNat) (hc : ComputableInPolyTime choices enc encBits) :
    ComputableInPolyTime (fun a => walk (w a) (h a) 0 (value a) (choices a)) enc
      (encOption (encPair encNat encNat)) := by
  have hs := encCursor_mk_polyTime hc (const 0) hv (const true)
  have hi := iterateWith_of_bounded_growth hw hh hs advance_polyTime
    (.const 12) (fun a s => growth (w a) s)
  have hf : ComputableInPolyTime finish encCursor (encOption (encPair encNat encNat)) :=
    ite encCursor_valid_deg.computableInPolyTime ((optionSome _).comp
      (encCursor_index_deg.computableInPolyTime.prod encCursor_value_deg.computableInPolyTime))
      (const none)
  apply (hf.comp hi).of_enc_eq
  intro a
  congr 1
  simp [finish_iterate]

/-- The entire parser is one fixed deterministic machine, including detection of invalid
subtotals, bit comparison, singleton selection and padding information. -/
theorem computableInPolyTime_route :
    ComputableInPolyTime (fun a : Input => route a.count a.bit a.claim a.choices) encInput
      (encOption (encPair encNat encNat)) := by
  have hh := binary_size.comp encInput_count_deg.computableInPolyTime
  have hw := unary_add' hh (const 1)
  have hc := encInput_choices_deg.computableInPolyTime
  have hv := bitsToNat.comp (bitsTakeWithInput hc hw)
  have hwalk := computableInPolyTime_walk hw hh hv (bitsDropWithInput hc hw)
  have hbit := decide_eq' (binary_testBit hv encInput_bit_deg.computableInPolyTime)
    encInput_claim_deg.computableInPolyTime
  apply (ite_decide hbit hwalk (const none)).of_enc_eq
  intro a
  congr 1
  simp [route, ofBits_eq_lsbValue]

private theorem repeat_round (w h : ℕ) :
    (fun xs : List Bool => (List.replicate w false ++ [true]) ++ xs)^[h] [] = rounds w h := by
  induction h with
  | zero => rfl
  | succ h ih => rw [Function.iterate_succ_apply', ih]; simp [rounds]

/-- Generate the subdivision flags in polynomial time in unary width and height. -/
theorem computableInPolyTime_rounds {α : Type} {enc : α ↪ List Bool} {w h : α → ℕ}
    (hw : ComputableInPolyTime w enc encUnary) (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun a => rounds (w a) (h a)) enc encBits := by
  let step := fun w (xs : List Bool) => (List.replicate w false ++ [true]) ++ xs
  have hs : ComputableInPolyTime (fun p : ℕ × List Bool => step p.1 p.2)
      (encPair encUnary encBits) encBits :=
    (((bitsReplicate false).comp (fst encUnary encBits)).bitsAppend (const [true])).bitsAppend
      (snd encUnary encBits)
  have hi := iterateWith_of_bounded_growth hw hh (const []) hs
    (hw.polyBounded.add (.const 1)) (fun _ _ => by simp [step, encBits_apply]; omega)
  apply hi.of_enc_eq
  intro a
  simp only [step, repeat_round]

/-- Generate every flag without enumerating the counted interval. -/
theorem computableInPolyTime_flags : ComputableInPolyTime flags encNat encBits := by
  have hh := binary_size
  have hw := unary_add' hh (const 1)
  exact ((bitsReplicate false).comp hw).bitsAppend (computableInPolyTime_rounds hw hh)

end Turing.MultiTapeATM.IntervalCountGame
