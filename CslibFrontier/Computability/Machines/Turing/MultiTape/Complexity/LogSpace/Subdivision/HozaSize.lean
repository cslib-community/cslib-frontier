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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Seed-independent size of Hoza's subdivision

Every seed uses the same rectangular carrier. The layout counts all chain slots, including
the unused ones, so the source and adjacency scans can share one dimension. The native
certificate computes the chain bound and both scan counts from the binary width and
horizon, using the actual generator code length and the final layer’s binary size.
-/

public section

namespace Cslib.Reachability.Hoza

open Turing.MultiTapeTM ComputableInSpace LayeredDigraph.Subdivision Code.JustesenFamily

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
  have hbase := budget_const (encB := encNat) 6 hin
  have hExp := budget_natAdd codeLength_inSpace (budget_comp_linear natSize (snd encNat encNat))
  have hbound : ComputableInSpace (fun p : ℕ × ℕ => generatedWeightBound p.1 p.2)
      (encPair encNat encNat) encNat (fun p => (encPair encNat encNat p).length) := by
    unfold generatedWeightBound
    apply budget_natPow_variable hbase hExp
    refine .of_le_linear (4 * (268435456 + 1)) (4 * (268435456 + 1) + 4) ?_
    intro p
    let e := codeLength p.1 p.2 + p.2.size
    have hc := codeLength_le_encodedDimensions p
    have hs : p.2.size ≤ (encPair encNat encNat p).length := by
      simp only [length_encPair, length_encNat_eq_size]
      omega
    have he : (encNat e).length ≤ e := by
      rw [length_encNat_eq_size, Nat.size_le]
      exact Nat.lt_two_pow_self
    change (e + 1) * (encNat 6).length + (encNat e).length + 1 ≤ _
    rw [show (encNat 6).length = 3 from rfl]
    dsimp only [e] at *
    omega
  exact encSubdivisionSize_mk_budget hcount hbound
    (budget_natMul hcount (budget_natSucc hbound))

end Cslib.Reachability.Hoza
