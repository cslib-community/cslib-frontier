/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Transport
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateLookup
import Mathlib.Data.List.GetD

/-!
# Executed successor tables under separate forward and inverse index maps

The raw program reads the old successor at the inverse input position and applies the forward
map to the result. A missing source entry returns the forward image of zero, exactly as in
the original program. The output length is an explicit actual graph/list count.

The transport identity reads every actual dart; it does not compute an inverse by choosing
one from an abstract equivalence. Ternary scope alignment uses an involution, while native
probe append uses separate maps moving two adjacent blocks in opposite directions.
-/

public section

namespace Cslib.Complexity.Graph.RotationCertificate

/-- Execute a raw table conjugation with independently computed forward and inverse maps.
Source indices and entries remain lookup data; only `count` funds the output enumeration. -/
@[expose] def reindex (c : RotationCertificate) (count : ℕ)
    (forward back : ℕ → ℕ) : RotationCertificate :=
  ⟨(List.range count).map fun i => forward (c.successor.getD (back i) 0)⟩

/-- Reindexing emits exactly its prescribed actual number of darts. -/
@[simp] theorem length_reindex (c : RotationCertificate) (count : ℕ)
    (forward back : ℕ → ℕ) : (reindex c count forward back).successor.length = count := by
  simp only [reindex, List.length_map, List.length_range]

/-- Each retained lookup is the literal transformed source lookup, including its
transformed-zero fallback on a missing or malformed source entry. -/
theorem getD_reindex (c : RotationCertificate) (count : ℕ) (forward back : ℕ → ℕ)
    {i : ℕ} (hi : i < count) :
    (reindex c count forward back).successor.getD i 0 = forward (c.successor.getD (back i) 0) := by
  rw [List.getD_eq_getElem _ _ (by rw [length_reindex]; exact hi)]
  simp only [reindex, List.getElem_map, List.getElem_range]

/-- The complete executed table represents the actual transported rotation when the two
native index maps agree with that dart equivalence and its inverse on actual positions. -/
theorem reindex_eq_ofRotation_transport {G H : Graph} (r : RotationSystem G)
    (c : RotationCertificate) (ht : ∀ a, c.successor.getD a.index 0 = (r.rotate a).index)
    (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (forward back : ℕ → ℕ)
    (hf : ∀ a, (e a).index = forward a.index)
    (hb : ∀ a, back (e a).index = a.index) :
    reindex c (2 * H.edges.length) forward back = ofRotation (r.transport e hv) := by
  symm
  apply (ofRotation_eq_iff _ _).mpr
  refine ⟨length_reindex _ _ _ _, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := e.surjective a
  have hi : (e b).index < 2 * H.edges.length := (Dart.indexEquiv H (e b)).isLt
  rw [getD_reindex _ _ _ _ hi, hb, ht]
  change forward (r.rotate b).index = ((e.permCongr r.rotate) (e b)).index
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact (hf (r.rotate b)).symm

end Cslib.Complexity.Graph.RotationCertificate
