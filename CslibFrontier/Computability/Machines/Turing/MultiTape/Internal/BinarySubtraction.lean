/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Subtraction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.ZipTransducer

/-!
# Binary subtraction zip transducer

This module retains the schoolbook borrow round as a raw zip transducer over little-endian binary
words. Missing digits are read as `false`. The transducer emits the raw difference digits and
leaves underflow to its caller rather than assigning a noncanonical natural-number result.

## Main definitions

* `Turing.MultiTapeTM.BinarySub.zipTransducer`: the retained schoolbook borrow transducer.

## Main results

* `Turing.MultiTapeTM.BinarySub.length_run_zipTransducer`: exact raw output length.
* `Turing.MultiTapeTM.BinarySub.ofBits_run_zipTransducer_of_le`: the raw digits encode natural
  subtraction when the right operand does not exceed the left.
-/

@[expose] public section

namespace Turing.MultiTapeTM.BinarySub

/-- The schoolbook binary-subtraction borrow round as a direct zip transducer. It emits the raw
little-endian difference digits; its final borrow is intentionally not emitted, so callers select
underflow separately before canonicalizing the raw word. -/
def zipTransducer : ZipTransducer Bool where
  q₀ := false
  step borrow digits :=
    subStep (borrow, []) (digits.1.getD false, digits.2.getD false)
  final _ := []
  length_step_le borrow digits := by
    simp [subStep]
  length_final_le _ := by simp

private theorem foldl_subStep_zipWithAll (acc : Bool × List Bool) :
    ∀ left right,
      ((List.zipWithAll (fun left right => (left.getD false, right.getD false))
        left right).foldl subStep acc).2 =
        acc.2 ++ zipTransducer.run acc.1 left right
  | [], [] => by rcases acc with ⟨borrow, out⟩; simp [zipTransducer]
  | bit :: left, [] => by
      rw [List.zipWithAll_nil, List.map_cons, List.foldl_cons,
        ZipTransducer.run_cons_nil]
      simp only [Option.getD_some, Option.getD_none]
      have ih := foldl_subStep_zipWithAll (subStep acc (bit, false)) left []
      simp only [List.zipWithAll_nil, Option.getD_some, Option.getD_none] at ih
      rw [ih]
      rcases acc with ⟨borrow, out⟩
      simp only [zipTransducer, subStep, Option.getD_some, Option.getD_none,
        List.nil_append, List.append_assoc]
  | [], bit :: right => by
      rw [List.nil_zipWithAll, List.map_cons, List.foldl_cons,
        ZipTransducer.run_nil_cons]
      simp only [Option.getD_some, Option.getD_none]
      have ih := foldl_subStep_zipWithAll (subStep acc (false, bit)) [] right
      simp only [List.nil_zipWithAll, Option.getD_some, Option.getD_none] at ih
      rw [ih]
      rcases acc with ⟨borrow, out⟩
      simp only [zipTransducer, subStep, Option.getD_some, Option.getD_none,
        List.nil_append, List.append_assoc]
  | leftBit :: left, rightBit :: right => by
      simp only [List.zipWithAll_cons_cons, List.foldl_cons, ZipTransducer.run_cons_cons,
        zipTransducer, Option.getD_some, subStep]
      rw [foldl_subStep_zipWithAll]
      rcases acc with ⟨borrow, out⟩
      simp only [zipTransducer, subStep, List.append_assoc, List.cons_append, List.nil_append]

/-- The raw subtraction transducer emits one digit for every position present in either input. -/
theorem length_run_zipTransducer (borrow : Bool) :
    ∀ left right, (zipTransducer.run borrow left right).length = max left.length right.length
  | [], [] => by simp [zipTransducer]
  | bit :: left, [] => by
      rw [ZipTransducer.run_cons_nil, List.length_append, length_run_zipTransducer]
      simp [zipTransducer, subStep]
      omega
  | [], bit :: right => by
      rw [ZipTransducer.run_nil_cons, List.length_append, length_run_zipTransducer]
      simp [zipTransducer, subStep]
      omega
  | leftBit :: left, rightBit :: right => by
      rw [ZipTransducer.run_cons_cons, List.length_append, length_run_zipTransducer]
      simp [zipTransducer, subStep]
      omega

private theorem foldr_fst_zipWithAll (left right : List Bool) :
    (((List.zipWithAll (fun left right => (left.getD false, right.getD false))
      left right).map Prod.fst).foldr Nat.bit 0) = ofBits left := by
  induction left generalizing right with
  | nil => simp [ofBits, List.map_map, Function.comp_def]
  | cons bit left ih =>
      cases right <;> simp [ofBits, List.map_map, Function.comp_def, ih]

private theorem foldr_snd_zipWithAll (left right : List Bool) :
    (((List.zipWithAll (fun left right => (left.getD false, right.getD false))
      left right).map Prod.snd).foldr Nat.bit 0) = ofBits right := by
  induction right generalizing left with
  | nil => simp [ofBits, List.map_map, Function.comp_def]
  | cons bit right ih =>
      cases left <;> simp [ofBits, List.map_map, Function.comp_def, ih]

/-- When the right operand does not exceed the left, the raw transducer digits encode their
natural-number difference. Callers select underflow separately. -/
theorem ofBits_run_zipTransducer_of_le (left right : List Bool)
    (hle : ofBits right ≤ ofBits left) :
    ofBits (zipTransducer.run false left right) = ofBits left - ofBits right := by
  let pairs := List.zipWithAll
    (fun left right => (left.getD false, right.getD false)) left right
  let result := pairs.foldl subStep (false, [])
  obtain ⟨digits, hdigits, hlength, hvalue⟩ := foldl_subStep pairs false []
  have hleft : (pairs.map Prod.fst).foldr Nat.bit 0 = ofBits left := by
    exact foldr_fst_zipWithAll left right
  have hright : (pairs.map Prod.snd).foldr Nat.bit 0 = ofBits right := by
    exact foldr_snd_zipWithAll left right
  have hdigitBound := Nat.foldr_bit_lt digits
  have hborrow : result.1 = false := by
    by_contra h
    have htrue : result.1 = true := Bool.eq_true_of_not_eq_false h
    simp only [result, hleft, hright, Bool.toNat_false, htrue, Bool.toNat_true] at hvalue
    rw [hlength] at hdigitBound
    omega
  have hrun : result.2 = zipTransducer.run false left right := by
    simpa only [result, List.nil_append] using
      foldl_subStep_zipWithAll (false, []) left right
  simp only [result, hleft, hright, Bool.toNat_false, hborrow, Nat.add_zero] at hvalue
  have hdigitsRun : zipTransducer.run false left right = digits := by
    rw [← hrun, hdigits, List.nil_append]
  rw [hdigitsRun]
  change digits.foldr Nat.bit 0 = ofBits left - ofBits right
  omega

end Turing.MultiTapeTM.BinarySub
