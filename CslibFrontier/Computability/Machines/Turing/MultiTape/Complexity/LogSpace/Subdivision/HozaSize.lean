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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Seed-independent size of Hoza's subdivision

Every seed uses the same rectangular carrier. The layout counts all chain slots, including
the unused ones, so the source and adjacency scans can share one dimension. The native
certificate computes the chain bound and both scan counts from the binary width and
horizon, using the actual generator code length and the final layer’s binary size.

`seedSearchSize` also computes the seed width and the exclusive binary rank limit needed
to start the outer counter. The exponent is linear in the encoded dimensions. The actual
candidate limit is written in binary.
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

/-- Size parameters shared across the seed counter and the subdivision scans. -/
structure SeedSearchSize where
  /-- The carrier used for every candidate seed. -/
  subdivision : SubdivisionSize
  /-- Number of bits in a seed. -/
  seedWidth : ℕ
  /-- Exclusive bound on candidate ranks. -/
  seedLimit : ℕ

/-- Framed subdivision parameters and seed width, followed by the binary seed limit. -/
enc_structure encSeedSearchSize : SeedSearchSize where
  subdivision : encSubdivisionSize, seedWidth : encNat, seedLimit : encNat

/-- Prepare the seed counter and its scan dimensions from binary width and horizon. -/
@[expose] def seedSearchSize (width horizon : ℕ) : SeedSearchSize :=
  let bits := codeLength width horizon
  ⟨subdivisionSize width horizon, bits, 2 ^ bits⟩

/-- The exclusive limit needs one more binary digit than the candidate ranks. -/
theorem length_seedSearchSize_seedLimit (width horizon : ℕ) :
    (encNat (seedSearchSize width horizon).seedLimit).length =
      (seedSearchSize width horizon).seedWidth + 1 := by
  simp only [seedSearchSize, length_encNat_two_pow]

/-- Initializing the sizes uses space linear in the encoded graph dimensions. The seed width
can be represented in unary within this budget, and the exclusive limit is written in binary. -/
theorem seedSearchSize_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => seedSearchSize p.1 p.2) (encPair encNat encNat)
      encSeedSearchSize (fun p => (encPair encNat encNat p).length) := by
  have hwidth := budget_comp (of_inO ComputableInO.natToUnary) codeLength_inSpace
    (.of_le_linear 268435456 268435456 fun p => by
      have hp := codeLength_le_encodedDimensions p
      omega)
  have hlimit := budget_comp_linear
    (of_inO (ComputableInDegree.two_pow_length encUnary).inO_one) hwidth
  exact encSeedSearchSize_mk_budget subdivisionSize_inSpace codeLength_inSpace
    (hlimit.of_enc_eq fun _ => by simp [encUnary_apply])

end Cslib.Reachability.Hoza
