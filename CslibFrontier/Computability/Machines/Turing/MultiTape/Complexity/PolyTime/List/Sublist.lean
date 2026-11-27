/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup

/-!
# Polynomial-time subsequence comparison

A left fold over the proposed supersequence consumes the head of the remaining pattern when
the next elements agree. The intermediate pattern is always a suffix of the original,
so its encoding cannot grow. This gives a native complexity certificate for `List.isSublist`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} [BEq α]

private def consumeHead (remaining : List α) (a : α) : List α :=
  if remaining.head? == some a then remaining.tail else remaining

private theorem foldl_consumeHead_isEmpty (pattern input : List α) :
    (input.foldl consumeHead pattern).isEmpty = pattern.isSublist input := by
  induction input generalizing pattern with
  | nil => cases pattern <;> rfl
  | cons a input ih =>
    cases pattern with
    | nil =>
      rw [List.foldl_cons, show consumeHead [] a = [] from rfl, ih]
      simp [List.isSublist]
    | cons b rest =>
      simp only [List.foldl_cons, ih, consumeHead, List.head?_cons, Option.some_beq_some,
        List.tail_cons, List.isSublist]
      by_cases h : (b == a) = true <;> simp [h]

/-- The standard Boolean subsequence test is polynomial-time with any framed element encoding. -/
theorem isSublist [LawfulBEq α] (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List α => p.1.isSublist p.2)
      (encPair (encList enc) (encList enc)) encBool := by
  have hhead := (head? enc).comp (fst (encList enc) enc)
  have hnext := (optionSome enc).comp (snd (encList enc) enc)
  have hstep : ComputableInPolyTime (fun p : List α × α => consumeHead p.1 p.2)
      (encPair (encList enc) enc) (encList enc) :=
    (beq hhead hnext).ite ((tail (encA := enc)).comp (fst _ _)) (fst _ _)
  have hfold := foldl_of_bounded_growth (growth := 0)
    (snd (encList enc) (encList enc)) (fst (encList enc) (encList enc)) hstep
    (fun remaining a => by
      unfold consumeHead
      split
      · simpa only [Nat.add_zero] using length_encList_sublist enc (List.tail_sublist remaining)
      · exact Nat.le_add_right _ _)
  convert (listIsEmpty (encA := enc)).comp hfold using 1
  funext p
  exact (foldl_consumeHead_isEmpty p.1 p.2).symm

end Turing.MultiTapeTM.ComputableInPolyTime
