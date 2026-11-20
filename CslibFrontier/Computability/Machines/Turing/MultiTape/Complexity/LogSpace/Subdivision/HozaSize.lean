/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator
public import CslibFrontier.Foundations.Combinatorics.Digraph.Layered.Subdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Seed-independent size of Hoza's subdivision

Every seed uses the same rectangular carrier. The layout counts all chain slots, including
the unused ones, so the source and adjacency scans can share one dimension. The native
certificate computes the chain bound and both scan counts from the binary width and
horizon, using the existing conservative polynomial bound on generated weights.
-/

public section

namespace Cslib.Reachability.Hoza

open Turing.MultiTapeTM ComputableInSpace LayeredDigraph.Subdivision

/-- Counts and the common chain bound retained across candidate seeds. -/
structure SubdivisionSize where
  /-- Number of original source vertices. -/
  originalCount : ℕ
  /-- Uniform upper bound on generated vertex weights. -/
  chainBound : ℕ
  /-- Total number of rectangular subdivision slots. -/
  vertexCount : ℕ

/-- Three binary naturals in field order, with the first two framed. -/
enc_structure encSubdivisionSize : SubdivisionSize where
  originalCount : encNat, chainBound : encNat, vertexCount : encNat

/-- Compute the shared source and subdivision dimensions from width and horizon. -/
@[expose] def subdivisionSize (width horizon : ℕ) : SubdivisionSize :=
  let originalCount := width * (horizon + 1)
  let chainBound := generatedWeightBound width horizon
  ⟨originalCount, chainBound, originalCount * (chainBound + 1)⟩

/-- The returned dimension counts the full rectangular carrier used by the scans. -/
theorem subdivisionSize_vertexCount (width horizon : ℕ) :
    (subdivisionSize width horizon).vertexCount =
      Nat.card (Vertex (Fin (horizon + 1) × Fin width)
        (subdivisionSize width horizon).chainBound) := by
  rw [card_vertex, Nat.card_prod, Nat.card_fin, Nat.card_fin]
  simp only [subdivisionSize, Nat.mul_comm width (horizon + 1)]

/-- All three size parameters fit in linear workspace in the binary width and horizon. -/
theorem subdivisionSize_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => subdivisionSize p.1 p.2) (encPair encNat encNat)
      encSubdivisionSize (fun p => (encPair encNat encNat p).length) := by
  have hin : (fun p => (encPair encNat encNat p).length) ≼
      (fun p => (encPair encNat encNat p).length) := .refl _
  have hcount := budget_natMul (fst encNat encNat) (budget_natSucc (snd encNat encNat))
  have hbase := budget_natMul (budget_const (encB := encNat) 2 hin) (budget_natSucc hcount)
  have hbound : ComputableInSpace (fun p : ℕ × ℕ => generatedWeightBound p.1 p.2)
      (encPair encNat encNat) encNat (fun p => (encPair encNat encNat p).length) := by
    unfold generatedWeightBound
    exact budget_natPow hbase hin _
  exact encSubdivisionSize_mk_budget hcount hbound
    (budget_natMul hcount (budget_natSucc hbound))

end Cslib.Reachability.Hoza
