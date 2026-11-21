/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededRankCapacity
public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat

/-!
# Dispatching the quantifier choices in a seeded rank challenge

A universal edge choice, existential rank guess, and universal bit index share a single
little-endian choice word in that order. A padded edge succeeds immediately. A genuine
edge first checks the rank bound. On a fitting rank, a padded bit index succeeds and a
genuine bit index issues the one required query to the native rank evaluator.
-/

public section

namespace Cslib.SeededRankChallenge

open Turing.MultiTapeTM ComputableInPolyTime BitString

/-- Graph size, coordinate count and the accumulated choices of the three moves. -/
structure Input where
  /-- Size of the edge universe. -/
  edges : ℕ
  /-- Number of alphabet-64 coordinates in each label. -/
  labelLength : ℕ
  /-- Little-endian edge, rank and bit-index words. -/
  choices : List Bool

/-- Edge count in binary, coordinate count in unary and choice word. -/
enc_structure encInput : Input where edges : encNat, labelLength : encUnary, choices : encBits

/-- The dispatcher receives only the two short numeric parameters and the accumulated choices. -/
theorem length_encInput (p : Input) : (encInput p).length =
    2 * p.edges.size + 2 * p.labelLength + p.choices.length + 2 := by
  simp [encInput_apply, encInputFields, encPair_apply, encNat_apply, Nat.size_eq_bits_len]
  omega

/-- One bit of the guessed rank of the selected edge. -/
structure Request where
  /-- Numbered edge. -/
  edge : ℕ
  /-- Index of the rank bit. -/
  bit : ℕ
  /-- Claimed value of this bit. -/
  claim : Bool
  deriving DecidableEq

/-- Two binary indices and the claimed bit. -/
enc_structure encRequest : Request where edge : encNat, bit : encNat, claim : encBool

/-- A terminal answer or a challenge for the native rank machine. -/
abbrev Result := Bool ⊕ Request

/-- The tag distinguishes a terminal answer from a rank query. -/
abbrev encResult := encSum encBool encRequest

/-- Challenge dispatch using a decoded edge, guess and bit index. The bit access is clamped
to the width on arbitrary inputs. Genuine bit queries read their exact supplied index. -/
@[expose] def dispatch (p : Input) (e g j : ℕ) : Result :=
  let w := Nat.clog 2 p.edges
  if e < p.edges then
    if SeededRankCapacity.fits ⟨p.edges, p.labelLength, g⟩ then
      if j < w then .inr ⟨e, j, g.testBit (min w j)⟩ else .inl true
    else .inl false
  else .inl true

/-- Decode the three little-endian choices and decide which machine is needed. -/
@[expose] def run (p : Input) : Result :=
  let w := Nat.clog 2 p.edges
  let rest := p.choices.drop w
  dispatch p (ofBits (p.choices.take w)) (ofBits (rest.take w)) (ofBits (rest.drop w))

private theorem ofBits_lowBits {w x : ℕ} (h : x < 2 ^ w) : ofBits (lowBits w x) = x :=
  (lsbValue_eq_foldr_bit _).symm.trans (lsbValue_lowBits h)

/-- On all padded choices, decoding recovers the move values and sends exactly the guessed
bit on each genuine rank query. The width may be zero. -/
theorem run_lowBits (N a e g j : ℕ)
    (he : e < 2 ^ Nat.clog 2 N) (hg : g < 2 ^ Nat.clog 2 N)
    (hj : j < 2 ^ Nat.clog 2 (Nat.clog 2 N)) :
    let w := Nat.clog 2 N
    run ⟨N, a, lowBits w e ++ (lowBits w g ++ lowBits (Nat.clog 2 w) j)⟩ =
      if e < N then
        if (g + 1) * 64 ^ (2 * a) ≤ 2 * N then
          if j < w then .inr ⟨e, j, g.testBit j⟩ else .inl true
        else .inl false
      else .inl true := by
  dsimp only
  have takeWord (w x : ℕ) (tail : List Bool) : (lowBits w x ++ tail).take w = lowBits w x := by
    conv_lhs => arg 1; rw [← length_lowBits w x]
    exact List.take_left
  have dropWord (w x : ℕ) (tail : List Bool) : (lowBits w x ++ tail).drop w = tail := by
    conv_lhs => arg 1; rw [← length_lowBits w x]
    exact List.drop_left
  simp only [run, takeWord, dropWord, ofBits_lowBits he, ofBits_lowBits hg, ofBits_lowBits hj,
    dispatch, SeededRankCapacity.fits_eq_true_iff]
  by_cases h : j < Nat.clog 2 N
  · simp [h, Nat.min_eq_right h.le]
  · simp [h]

/-- All framing, choice decoding, capacity arithmetic and bit extraction have polynomial cost
on the short input to the choice dispatcher. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput encResult := by
  have hn := encInput_edges_deg.computableInPolyTime
  have ha := encInput_labelLength_deg.computableInPolyTime
  have hw := binary_clog_two.comp hn
  have hc := encInput_choices_deg.computableInPolyTime
  have hrest := bitsDropWithInput hc hw
  have he := bitsToNat.comp (bitsTakeWithInput hc hw)
  have hg := bitsToNat.comp (bitsTakeWithInput hrest hw)
  have hj := bitsToNat.comp (bitsDropWithInput hrest hw)
  have hfits := SeededRankCapacity.computableInPolyTime_fits.comp
    (SeededRankCapacity.encInput_mk_polyTime hn ha hg)
  have hrequest := (sumInr encBool encRequest).comp
    (encRequest_mk_polyTime he hj (binary_testBit hg (binary_min_unary' hw hj)))
  have hyes : ComputableInPolyTime (fun _ : Input => Sum.inl true) encInput encResult := const _
  have hno : ComputableInPolyTime (fun _ : Input => Sum.inl false) encInput encResult := const _
  exact ite_decide (binary_lt' he hn)
    (ite hfits (ite_decide (binary_lt' hj (unary_to_binary.comp hw)) hrequest hyes) hno) hyes

end Cslib.SeededRankChallenge
