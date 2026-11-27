/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Complexity.Classes.PP.Characterization
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime

/-!
# Vyalyi's counting class A₀PP

[Vyalyi][Vyalyi2003], Definition 2, uses a GapP function and an input-dependent FP threshold.
The integer inequality `2 * g x < T x` expresses the strict half-threshold on nonmembers.
Subtracting the threshold gives the inclusion in PP.

## References

* [M. Vyalyi, *QMA = PP implies that PP contains PH*][Vyalyi2003], ECCC TR03-021.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **A₀PP** [Vyalyi][Vyalyi2003], Definition 2. A GapP function exceeds a binary FP threshold
on members. On nonmembers it is nonnegative and strictly below half that threshold. -/
@[expose] def A0PP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ g ∈ GapP enc, ∃ T : α → ℤ, ComputableInPolyTime T enc encIntBin ∧
    ∀ a, (a ∈ A → T a < g a) ∧ (a ∉ A → 0 ≤ g a ∧ 2 * g a < T a)}

/-- **A₀PP ⊆ PP** [Vyalyi][Vyalyi2003], following Definition 2. The difference of the gap
function and its FP threshold is positive exactly on members. -/
theorem A0PP_subset_PP : A0PP enc ⊆ PP enc := by
  rintro A ⟨g, hg, T, hT, hA⟩
  refine mem_PP_iff_exists_GapP.mpr ⟨_, GapP.sub_mem' hg (mem_GapP_of_polyTime hT), fun a => ?_⟩
  change a ∈ A ↔ 0 < g a - T a
  refine ⟨fun ha => sub_pos.mpr ((hA a).1 ha), fun h => by_contra fun ha => ?_⟩
  obtain ⟨hn, ht⟩ := (hA a).2 ha
  omega

end Cslib.Complexity
