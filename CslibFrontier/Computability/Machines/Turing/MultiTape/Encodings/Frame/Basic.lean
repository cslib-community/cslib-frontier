/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import CslibFrontier.Computability.Encoding.Delimit
public import Mathlib.Data.List.Basic

/-! # Pure framed words

Machine-facing names for the shared delimited-word API. These reducible aliases preserve
encoded words and existing machine specifications; generic parsing proofs live in `Cslib.Encoding`.
-/

namespace Turing.MultiTapeTM

/-! ### Framed words -/

/-- Each symbol `b` of `w` as `[true, b]`, followed by `[false]`. -/
public abbrev frame : List Bool → List Bool :=
  Cslib.Encoding.delimit

/-- The word framed at the start of a bit word. -/
public abbrev unframe : List Bool → List Bool :=
  Cslib.Encoding.undelimit

/-- What follows the frame at the start of a bit word. -/
public abbrev dropFrame : List Bool → List Bool :=
  Cslib.Encoding.dropDelimited

@[simp]
public lemma frame_nil : frame [] = [false] := rfl

@[simp]
public lemma frame_cons (b : Bool) (w : List Bool) : frame (b :: w) = true :: b :: frame w := rfl

@[simp]
public lemma length_frame (w : List Bool) : (frame w).length = 2 * w.length + 1 :=
  Cslib.Encoding.length_delimit w

/-- Framing a unary block doubles its run of `true` bits before the delimiter. -/
public lemma frame_replicate_true (n : ℕ) :
    frame (List.replicate n true) = List.replicate (2 * n) true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, frame_cons, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    rfl

@[simp]
public lemma unframe_frame_append (w u : List Bool) : unframe (frame w ++ u) = w :=
  Cslib.Encoding.undelimit_delimit_append w u

@[simp]
public lemma unframe_frame (w : List Bool) : unframe (frame w) = w :=
  Cslib.Encoding.undelimit_delimit w

@[simp]
public lemma dropFrame_frame_append (w u : List Bool) : dropFrame (frame w ++ u) = u :=
  Cslib.Encoding.dropDelimited_delimit_append w u

/-- A framed word followed by another word determines both. -/
public theorem frame_append_inj {w w' u u' : List Bool} (h : frame w ++ u = frame w' ++ u') :
    w = w' ∧ u = u' :=
  Cslib.Encoding.delimit_append_inj h

/-- Framing is injective. -/
public theorem frame_injective : Function.Injective frame :=
  Cslib.Encoding.delimit_injective

@[simp]
public lemma frame_ne_nil (w : List Bool) : frame w ≠ [] :=
  Cslib.Encoding.delimit_ne_nil w

end Turing.MultiTapeTM
