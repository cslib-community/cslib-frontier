/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredParameters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.HozaSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute

/-!
# Seed-search initialization from the original configuration-graph input

The native initializer counts the original input through the existing layered STCON routine.
It retains the resulting graph parameters and computes the common subdivision size, seed width
and exclusive rank limit from the graph's width and final layer. The encoded result fits in
logarithmic space in the original word length. This prepares the parameters used by a later
scanner that queries the original input.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open Reachability.Hoza

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

/-- The arithmetic stage needs only space linear in the compact graph parameters. -/
theorem seedSearchParameters_inSpace :
    ComputableInSpace seedSearchParameters encLayeredParameters encSeedSearchParameters
      (fun p => (encLayeredParameters p).length) := by
  have hid := budget_id (BigOLe.refl fun p => (encLayeredParameters p).length)
  have hw := encLayeredParameters_width_budget hid
  have hdims := budget_prod hw (budget_natPred hw)
  have hs := budget_comp_linear seedSearchSize_inSpace hdims
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

end Cslib.Complexity.STCON
