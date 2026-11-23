/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.Language

/-!
# The copy language

The copy language consists of words `x ++ x`, with no separator between the two copies.
The alphabet is arbitrary. Splitting a word into two equal-length parts reduces membership to
equality of the parts (`Cslib.Language.append_mem_copy_iff`); this is the interface used by
single-tape crossing-sequence lower bounds.

## Main definitions

* `Cslib.Language.copy`: the language of two consecutive copies of the same word.

## Main results

* `Cslib.Language.append_mem_copy_iff`: equal-length parts form a copy word exactly when equal.
-/

public section

namespace Cslib.Language

/-- The language `{x ++ x | x : List α}`, without a separator. In particular, it contains the
empty word. -/
@[expose] def copy (α : Type*) : _root_.Language α := {w | ∃ x, w = x ++ x}

/-- Two equal-length words concatenate to a copy word exactly when they are equal. -/
theorem append_mem_copy_iff {α : Type*} {u v : List α} (h : u.length = v.length) :
    u ++ v ∈ copy α ↔ u = v := by
  constructor
  · rintro ⟨x, hx⟩
    have hlen := congrArg List.length hx
    simp only [List.length_append] at hlen
    have hux : u.length = x.length := by omega
    obtain ⟨hu, hv⟩ := List.append_inj hx hux
    exact hu.trans hv.symm
  · rintro rfl
    exact ⟨u, rfl⟩

end Cslib.Language
