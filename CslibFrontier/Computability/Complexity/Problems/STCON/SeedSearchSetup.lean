/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedSearchParameters
public import CslibFrontier.Computability.Complexity.Problems.STCON.SubdivisionEndpoints
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute

/-!
# Initial data for the subdivided STCON seed search

The initializer returns the retained graph and seed-search parameters together with the
fixed source and target IDs. Both IDs are computed using the same chain bound as the
returned scan carrier. The setup uses logarithmic native workspace on the original input
and returns logarithmically many bits.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open Reachability.Hoza Cslib.LayeredDigraph.Subdivision

/-- The retained parameters and fixed endpoints for the subdivision scan. -/
structure SeedSearchSetup where
  /-- Graph parameters, subdivision dimensions, and seed counter limit. -/
  parameters : SeedSearchParameters
  /-- Flat ID of the designated source root. -/
  sourceID : ℕ
  /-- Flat ID of the target root. -/
  targetID : ℕ

/-- Frame the retained search parameters and binary source ID, then append the binary target ID. -/
enc_structure encSeedSearchSetup : SeedSearchSetup where
  parameters : encSeedSearchParameters, sourceID : encNat, targetID : encNat

private def setup (p : SeedSearchParameters) : SeedSearchSetup :=
  let ids := subdivisionEndpointIDs (p.graph, p.search.subdivision.chainBound)
  ⟨p, ids.1, ids.2⟩

private theorem setup_inSpace :
    ComputableInSpace setup encSeedSearchParameters encSeedSearchSetup
      (fun p => (encSeedSearchParameters p).length) := by
  have hid := budget_id (enc := encSeedSearchParameters) (.refl _)
  have hg := encSeedSearchParameters_graph_budget hid
  have hs := encSeedSearchParameters_search_budget hid
  have hb := encSubdivisionSize_chainBound_budget (encSeedSearchSize_subdivision_budget hs)
  have hids := budget_comp_linear subdivisionEndpointIDs_inSpace (budget_prod hg hb)
  let encIDs := encPair encNat encNat
  have hp := fst encSeedSearchParameters encIDs
  have he := snd encSeedSearchParameters encIDs
  have hmk := encSeedSearchSetup_mk_budget hp
    (budget_comp_linear (fst encNat encNat) he) (budget_comp_linear (snd encNat encNat) he)
  have h := budget_comp_linear hmk (budget_prod hid hids)
  exact h

variable {k : ℕ} {State : Type} [Fintype State]

/-- Initialize the search dimensions and both endpoints from the original read-only input. -/
noncomputable def configurationSeedSearchSetup (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) : SeedSearchSetup :=
  setup (configurationSeedSearchParameters ntm c w)

/-- The initializer retains the existing parameters and returns the two indexed roots
from their subdivision carrier. -/
theorem configurationSeedSearchSetup_endpoints (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let p := configurationSeedSearchParameters ntm c w
    let bound := p.search.subdivision.chainBound
    let index := subdivisionIndex I bound
    let s := configurationSeedSearchSetup ntm c w
    s.parameters = p ∧ (s.sourceID, s.targetID) =
      ((index (root bound (layeredCoordinates I (layeredStart I)))).val,
        (index (root bound (layeredCoordinates I (layeredTarget I)))).val) := by
  exact ⟨rfl, subdivisionEndpointIDs_eq ntm c w _⟩

/-- The two fixed endpoint IDs are valid positions in the returned scan carrier. -/
theorem configurationSeedSearchSetup_endpoints_lt_vertexCount (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let s := configurationSeedSearchSetup ntm c w
    let n := s.parameters.search.subdivision.vertexCount
    s.sourceID < n ∧ s.targetID < n := by
  obtain ⟨hparams, hids⟩ := configurationSeedSearchSetup_endpoints ntm c w
  let I := configurationInstance ntm c w
  let p := configurationSeedSearchParameters ntm c w
  let bound := p.search.subdivision.chainBound
  let index := subdivisionIndex I bound
  have hcount : p.search.subdivision.vertexCount = (((I.n - 1) + 1) * I.n) * (bound + 1) := by
    have h := subdivisionSize_vertexCount I.n (I.n - 1)
    rw [card_vertex, Nat.card_prod, Nat.card_fin, Nat.card_fin] at h
    exact h
  dsimp only
  rw [hparams, hcount]
  rw [(Prod.mk.inj hids).1, (Prod.mk.inj hids).2]
  exact ⟨(index _).isLt, (index _).isLt⟩

/-- The entire setup is computed natively in logarithmic workspace on the original input. -/
theorem configurationSeedSearchSetup_inLogSpace (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInLogSpace (configurationSeedSearchSetup ntm c) encBits encSeedSearchSetup :=
  comp_logSpace_of_length_log (f := configurationSeedSearchParameters ntm c) (g := setup)
    (configurationSeedSearchParameters_inLogSpace ntm c)
    (length_configurationSeedSearchParameters_le_log ntm c) setup_inSpace

/-- The retained setup fits in logarithmically many bits in the original input length. -/
theorem length_configurationSeedSearchSetup_le_log (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      (encSeedSearchSetup (configurationSeedSearchSetup ntm c w)).length ≤
        C * (Nat.log2 w.length + 1) :=
  length_log_of_inSpace (encIn := encBits) (f := configurationSeedSearchParameters ntm c)
    (g := setup) (length_configurationSeedSearchParameters_le_log ntm c) setup_inSpace

end Cslib.Complexity.STCON
