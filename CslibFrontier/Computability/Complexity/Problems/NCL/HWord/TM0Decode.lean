/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.TM0Rules

/-!
# Decoding phased tape words

The side tags determine the inactive tape cells. The remaining one or two control letters
identify the transfer phase and its state.

## Main results

* `TM0Window.Rules.word_injective`: each phased configuration has a unique word.
-/

public section

namespace Cslib.Complexity.NCL.TM0Window.Rules
open Cslib.PostCorrespondence.OfTM0.Letter
variable {Γ Q : Type*} [DecidableEq Q]

private def readRight : List (Symbol Γ Q) → Option (List Γ)
  | [rb] => some []
  | sym (a, true) :: w => (readRight w).map (a :: ·)
  | _ => none

private def scan (L : List Γ) : List (Symbol Γ Q) → Option (MicroCfg Γ Q)
  | sym (a, false) :: w => scan (a :: L) w
  | cell (.running q) (a, false) :: w =>
      (readRight w).map fun R => .stable ⟨q, a, L, R⟩
  | cell (.rightFirst q) (a, false) :: sym (b, true) :: w =>
      (readRight w).map fun R => .moving .rightStart ⟨q, a, b, L, R⟩
  | cell (.rightFirst q) (a, false) :: cell (.rightSecond q') (b, false) :: w =>
      if q = q' then (readRight w).map fun R => .moving .rightBoth ⟨q, a, b, L, R⟩ else none
  | cell (.leftFirst q) (a, false) :: sym (b, true) :: w =>
      (readRight w).map fun R => .moving .leftEnd ⟨q, a, b, L, R⟩
  | cell (.leftFirst q) (a, false) :: cell (.leftSecond q') (b, false) :: w =>
      if q = q' then (readRight w).map fun R => .moving .leftBoth ⟨q, a, b, L, R⟩ else none
  | cell (.rightSecond q) (b, false) :: w =>
      match L with
      | a :: L => (readRight w).map fun R => .moving .rightEnd ⟨q, a, b, L, R⟩
      | [] => none
  | cell (.leftSecond q) (b, false) :: w =>
      match L with
      | a :: L => (readRight w).map fun R => .moving .leftStart ⟨q, a, b, L, R⟩
      | [] => none
  | _ => none

private def decode : List (Symbol Γ Q) → Option (MicroCfg Γ Q)
  | lb :: w => scan [] w
  | _ => none

omit [DecidableEq Q] in
private theorem readRight_map (R : List Γ) :
    readRight (R.map (fun a => (sym (a, true) : Symbol Γ Q)) ++ [rb]) = some R := by
  induction R with
  | nil => rfl
  | cons a R ih => simp only [List.map_cons, List.cons_append, readRight, ih, Option.map_some]

private theorem scan_prefix (L A : List Γ) (w : List (Symbol Γ Q)) :
    scan A (L.reverse.map (fun a => (sym (a, false) : Symbol Γ Q)) ++ w) = scan (L ++ A) w := by
  induction L generalizing A w with
  | nil => rfl
  | cons a L ih =>
    calc
      _ = scan A (L.reverse.map (fun a => (sym (a, false) : Symbol Γ Q)) ++
          sym (a, false) :: w) := by
        simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.cons_append, List.nil_append]
      _ = scan (L ++ A) (sym (a, false) :: w) := ih A _
      _ = scan ((a :: L) ++ A) w := rfl

private theorem decode_frame (L R : List Γ) (middle : List (Symbol Γ Q)) :
    decode (frame L middle R) =
      scan L (middle ++ R.map (fun a => sym (a, true)) ++ [rb]) := by
  simp only [frame, decode, List.append_assoc, scan_prefix, List.append_nil]

private theorem decode_word (c : MicroCfg Γ Q) : decode (word c) = some c := by
  cases c with
  | stable c =>
    rcases c with ⟨q, a, L, R⟩
    simp only [word, decode_frame, List.cons_append, List.nil_append, scan, readRight_map,
      Option.map_some]
  | moving phase c =>
    rcases c with ⟨q, a, b, L, R⟩
    cases phase <;>
      simp only [word, decode_frame, List.cons_append, List.nil_append, scan, readRight_map,
        Option.map_some, ↓reduceIte]

omit [DecidableEq Q] in
/-- A tape word determines its complete phased configuration. -/
theorem word_injective : Function.Injective (word (Γ := Γ) (Q := Q)) := by
  classical
  intro c d h
  have h' := congrArg decode h
  simpa only [decode_word, Option.some.injEq] using h'

end Cslib.Complexity.NCL.TM0Window.Rules
