/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomially balanced images of PSPACE languages

A bounded search for a source word transfers polynomial space along a polynomial-time function.
The function need not be injective and no efficient inverse is assumed. The source-length bound
is required only on accepted source words. This generalizes the application-specific argument in
`lean-canny` at revision `12ea037`, using the existing plain machine interfaces.
## Main results

* `Cslib.Complexity.bounded_image_mem_PSPACE`: polynomially balanced images preserve PSPACE,
  without injectivity or an efficient inverse.

-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The image of a PSPACE language under a polynomial-time function is in PSPACE when accepted
source words have a polynomial-time unary length bound computed from their images. -/
theorem bounded_image_mem_PSPACE {L : Set (List Bool)} {f : List Bool → List Bool}
    (hL : L ∈ PSPACE encBits) (hf : ComputableInPolyTime f encBits encBits)
    {bound : List Bool → ℕ} (hb : ComputableInPolyTime bound encBits encUnary)
    (hbalance : ∀ w ∈ L, w.length ≤ bound (f w)) : f '' L ∈ PSPACE encBits := by
  have hc : ComputableInPolyTime (fun p : List Bool × List Bool => unframe p.2)
      (encPair encBits encBits) encBits := .comp .unframe (.snd _ _)
  have hsource : {p : List Bool × List Bool | unframe p.2 ∈ L} ∈
      PSPACE (encPair encBits encBits) :=
    PolyTimeReducible.mem_PSPACE ⟨_, hc, fun _ => Iff.rfl⟩ hL
  have heq : {p : List Bool × List Bool | f (unframe p.2) = p.1} ∈
      P (encPair encBits encBits) :=
    ⟨_, .decide_eq' (hf.comp hc) (.fst _ _), fun _ => by simp⟩
  convert setOf_exists_mem_PSPACE (inter_mem_PSPACE hsource (P_subset_PSPACE heq))
    (by fun_prop : ComputableInPolyTime (fun y => 2 * bound y + 1) encBits encUnary) using 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff]
  refine ⟨?_, fun ⟨w, _, hw, he⟩ => ⟨unframe w, hw, he⟩⟩
  rintro ⟨w, hw, rfl⟩
  refine ⟨frame w ++ List.replicate (2 * bound (f w) - 2 * w.length) false, ?_,
    by simpa only [unframe_frame_append] using hw, by simp only [unframe_frame_append]⟩
  have := hbalance w hw
  simp only [List.length_append, length_frame, List.length_replicate]
  omega

end Cslib.Complexity
