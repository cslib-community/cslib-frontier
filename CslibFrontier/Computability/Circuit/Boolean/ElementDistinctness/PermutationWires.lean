/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.RoutingNetwork

/-!
# Pinning permutations on a shared routing network

Fix one permutation of the records in each list. Every input payload bit is then constrained
to equal just the bit at its assigned output. The graph, the input sites and the output sites
are independent of the permutations. This gives the fixed topology in the “Uniform destinations”
lemma of [OpenAI2026MatrixExponentNineFourths].
-/

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Finset Frontier

/-- One payload wire, indexed by its list, record and bit within that record. -/
public abbrev RoutingSlot (t h : ℕ) := Fin t × Fin (2 ^ h) × Fin h

private def payloadLeg (t h : ℕ) :
    RoutingSlot t h ⊕ RoutingSlot t h ↪ Fin t × RoutingBit h where
  toFun
    | .inl (a, i, b) => (a, .input i b)
    | .inr (a, i, b) => (a, .output i b)
  inj' := by
    rintro (⟨a, i, b⟩ | ⟨a, i, b⟩) (⟨c, j, d⟩ | ⟨c, j, d⟩) he <;> simp_all

open scoped Classical in
/-- Pinning the tags to arbitrary per-list permutations turns a joint routing network into their
independent payload wires. Both endpoint sites, and the internal multigraph, agree for every
choice of the permutations. -/
public theorem exists_permutationWires_of_taggedPermutation
    {R V E : Type*} [CommSemiring R] [Fintype V] [Fintype E] [DecidableEq E] {t h : ℕ}
    (N : OpenBitNetwork R (Fin t × RoutingBit h) V E) (hN : N.Trivalent)
    (hT : ∀ z, N.contraction z =
      ∏ a : Fin t, if TaggedPermutation (fun q => z (a, q)) then 1 else 0)
    (π : Fin t → Equiv.Perm (Fin (2 ^ h))) :
    ∃ M : OpenBitNetwork R (RoutingSlot t h ⊕ RoutingSlot t h) V E,
      M.toMultigraph = N.toMultigraph ∧ M.Trivalent ∧ M.volume ≤ N.volume ∧
      (∀ a i b, M.site (.inl (a, i, b)) = N.site (a, .input i b) ∧
        M.site (.inr (a, i, b)) = N.site (a, .output i b)) ∧
      ∀ z, M.contraction z =
        ∏ s : RoutingSlot t h,
          let (a, i, b) := s
          if z (.inl (a, i, b)) = z (.inr (a, π a i, b)) then 1 else 0 := by
  classical
  let fill : Fin t × RoutingBit h → Bool
    | (a, .tag i b) => (BitString.equivFin h).symm (π a i) b
    | _ => false
  let e := payloadLeg t h
  obtain ⟨M, hgraph, hsite, htri, hvol, hpin⟩ := N.exists_pin hN e fill
  refine ⟨M, hgraph, htri, hvol, fun a i b =>
    ⟨congrFun hsite (.inl (a, i, b)), congrFun hsite (.inr (a, i, b))⟩, fun z => ?_⟩
  rw [hpin, hT, Fintype.prod_prod_type]
  refine prod_congr rfl fun a _ => ?_
  have tag (i : Fin (2 ^ h)) (b : Fin h) :
      Function.extend e z fill (a, .tag i b) = (BitString.equivFin h).symm (π a i) b := by
    apply Function.extend_apply'
    rintro ⟨(⟨_, _, _⟩ | ⟨_, _, _⟩), he⟩ <;> cases he
  have dest (i : Fin (2 ^ h)) :
      BitString.equivFin h (fun b => Function.extend e z fill (a, .tag i b)) = π a i :=
    (congrArg (BitString.equivFin h) (funext (tag i))).trans
      ((BitString.equivFin h).apply_symm_apply _)
  have input (i : Fin (2 ^ h)) (b : Fin h) :
      Function.extend e z fill (a, .input i b) = z (.inl (a, i, b)) :=
    e.injective.extend_apply z fill (.inl (a, i, b))
  have output (i : Fin (2 ^ h)) (b : Fin h) :
      Function.extend e z fill (a, .output i b) = z (.inr (a, i, b)) :=
    e.injective.extend_apply z fill (.inr (a, i, b))
  simp [TaggedPermutation, dest, input, output, Fintype.prod_boole, Prod.forall]

end Cslib.Circuits.Boolean.ElementDistinctness
