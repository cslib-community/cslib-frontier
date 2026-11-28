/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Complexity.Classes.PP.Oracle.Space

/-!
# Counting levels within polynomial space

A strict polynomial-time majority verifier with a polynomial-space language oracle can be
evaluated in polynomial space. Each query is answered by the oracle's actual decider, and a
binary counter enumerates witnesses while reusing its workspace. Exact ties reject.
Induction then puts every fixed counting level in PSPACE.

## Main results

* `Cslib.Complexity.CountingLevel_subset_PSPACE`: every fixed counting level is in PSPACE.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- Each fixed counting level is decidable within polynomial space. The level is fixed for the
language, rather than supplied as an input-dependent oracle depth. -/
theorem CountingLevel_subset_PSPACE (a : ℕ) : CountingLevel a enc ⊆ PSPACE enc := by
  induction a generalizing α with
  | zero => exact P_subset_PSPACE
  | succ a ih =>
    rintro L ⟨A, hA, hL⟩
    exact PPWithOracle_subset_PSPACE (ih hA) hL

end Cslib.Complexity
