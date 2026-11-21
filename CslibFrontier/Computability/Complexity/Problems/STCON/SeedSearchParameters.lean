/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredParameters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.HozaSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

/-!
# Seed-search initialization from the original configuration-graph input

The native initializer counts the original input through the existing layered STCON routine.
It retains the resulting graph parameters and computes the common subdivision size, seed width
and exclusive rank limit from the graph's width and final layer. The encoded result fits in
logarithmic space in the original word length. This prepares the parameters used by a later
scanner that queries the original input. The same length bound controls the numeric seed
limit, source count and subdivision carrier size by a polynomial in the original word length.
The same square dimensions initialize the Justesen field context in native logarithmic space.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open Reachability.Hoza Cslib.Code.JustesenFamily

/-- Compact parameters for the original graph and its seed search. -/
structure SeedSearchParameters where
  /-- Parameters shared by the original layered adjacency queries. -/
  graph : LayeredParameters
  /-- Carrier and seed dimensions shared by the isolation search. -/
  search : SeedSearchSize

/-- Framed graph parameters followed by the binary search sizes. -/
enc_structure encSeedSearchParameters : SeedSearchParameters where
  graph : encLayeredParameters, search : encSeedSearchSize

/-- Retain the graph parameters and compute the seed-search sizes for its square layering. -/
@[expose] def seedSearchParameters (p : LayeredParameters) : SeedSearchParameters :=
  ⟨p, seedSearchSize p.width (p.width - 1)⟩

private theorem widthHorizon_inSpace :
    ComputableInSpace (fun p : LayeredParameters => (p.width, p.width - 1))
      encLayeredParameters (encPair encNat encNat) (fun p => (encLayeredParameters p).length) := by
  have hw := encLayeredParameters_width_budget (budget_id (.refl _))
  exact budget_prod hw (budget_natPred hw)

/-- The arithmetic stage needs only space linear in the compact graph parameters. -/
theorem seedSearchParameters_inSpace :
    ComputableInSpace seedSearchParameters encLayeredParameters encSeedSearchParameters
      (fun p => (encLayeredParameters p).length) := by
  have hid := budget_id (BigOLe.refl fun p => (encLayeredParameters p).length)
  have hs := budget_comp_linear seedSearchSize_inSpace widthHorizon_inSpace
  exact encSeedSearchParameters_mk_budget hid hs

variable {k : ℕ} {State : Type} [Fintype State]

/-- Initialize both the graph and seed-search parameters from the raw input length. -/
@[expose] noncomputable def configurationSeedSearchParameters
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : SeedSearchParameters :=
  seedSearchParameters (layeredParameters ntm c w.length)

/-- A single native initializer uses logarithmic workspace on the original input. -/
theorem configurationSeedSearchParameters_inLogSpace (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInLogSpace (configurationSeedSearchParameters ntm c)
      encBits encSeedSearchParameters :=
  comp_logSpace_of_length_log (f := fun w : List Bool => layeredParameters ntm c w.length)
    (g := seedSearchParameters) (layeredParameters_inLogSpace ntm c)
    (length_layeredParameters_le_log ntm c) seedSearchParameters_inSpace

/-- The complete initialized record, including the seed counter limit, fits in logarithmic
encoded length on the original input. -/
theorem length_configurationSeedSearchParameters_le_log (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      (encSeedSearchParameters (configurationSeedSearchParameters ntm c w)).length ≤
        C * (Nat.log2 w.length + 1) :=
  length_log_of_inSpace (encIn := encBits)
    (f := fun w : List Bool => layeredParameters ntm c w.length) (g := seedSearchParameters)
    (length_layeredParameters_le_log ntm c)
    seedSearchParameters_inSpace

/-- Prepare the Justesen field data for the square layering of the configuration graph. -/
@[expose] noncomputable def configurationFieldContext (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) : FieldContext :=
  let width := (layeredParameters ntm c w.length).width
  fieldContext width (width - 1)

private theorem layeredFieldContext_inSpace :
    ComputableInSpace (fun p : LayeredParameters => fieldContext p.width (p.width - 1))
      encLayeredParameters encFieldContext (fun p => (encLayeredParameters p).length) :=
  budget_comp_linear fieldContext_inSpace widthHorizon_inSpace

/-- The actual Justesen field context can be initialized in native logarithmic workspace
from the original read-only word. -/
theorem configurationFieldContext_inLogSpace (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInLogSpace (configurationFieldContext ntm c) encBits encFieldContext :=
  comp_logSpace_of_length_log (f := fun w : List Bool => layeredParameters ntm c w.length)
    (layeredParameters_inLogSpace ntm c) (length_layeredParameters_le_log ntm c)
    layeredFieldContext_inSpace

/-- The prepared field context occupies logarithmically many bits for the original word. -/
theorem length_configurationFieldContext_le_log (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      (encFieldContext (configurationFieldContext ntm c w)).length ≤
        C * (Nat.log2 w.length + 1) :=
  length_log_of_inSpace (encIn := encBits)
    (f := fun w : List Bool => layeredParameters ntm c w.length)
    (length_layeredParameters_le_log ntm c) layeredFieldContext_inSpace

/-- The initialized seed limit, original-source count and subdivided vertex count are
polynomial in the original input length. These numeric bounds can be used in a clock for
the nested seed and source loops. -/
theorem configurationSeedSearchParameters_polyBounded (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) :
    PolyBounded List.length (fun w =>
      (configurationSeedSearchParameters ntm c w).search.seedLimit) ∧
    PolyBounded List.length (fun w =>
      (configurationSeedSearchParameters ntm c w).search.subdivision.originalCount) ∧
    PolyBounded List.length (fun w =>
      (configurationSeedSearchParameters ntm c w).search.subdivision.vertexCount) := by
  obtain ⟨C, hC⟩ := length_configurationSeedSearchParameters_le_log ntm c
  have hpoly (f : SeedSearchParameters → ℕ)
      (hf : ∀ p, (encNat (f p)).length ≤ (encSeedSearchParameters p).length) :
      PolyBounded List.length (fun w => f (configurationSeedSearchParameters ntm c w)) := by
    refine (PolyBounded.of_polynomiallyBounded List.length
      (polynomiallyBounded_two_pow_mul_log C)).mono fun w => ?_
    have hlen := (hf (configurationSeedSearchParameters ntm c w)).trans (hC w)
    rw [length_encNat_eq_size, Nat.log2_eq_log_two] at hlen
    exact (Nat.size_le.mp hlen).le
  have hsub (p : SeedSearchParameters) :
      (encSubdivisionSize p.search.subdivision).length ≤ (encSeedSearchParameters p).length :=
    (encSeedSearchSize_subdivision_length_le p.search).trans
      (encSeedSearchParameters_search_length_le p)
  exact ⟨hpoly (fun p => p.search.seedLimit) fun p =>
      (encSeedSearchSize_seedLimit_length_le p.search).trans
        (encSeedSearchParameters_search_length_le p),
    hpoly (fun p => p.search.subdivision.originalCount) fun p =>
      (encSubdivisionSize_originalCount_length_le p.search.subdivision).trans (hsub p),
    hpoly (fun p => p.search.subdivision.vertexCount) fun p =>
      (encSubdivisionSize_vertexCount_length_le p.search.subdivision).trans (hsub p)⟩

end Cslib.Complexity.STCON
