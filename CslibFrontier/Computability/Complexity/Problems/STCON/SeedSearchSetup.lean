/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.SeedSearch.OriginalRoots
public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedSearchParameters
public import CslibFrontier.Computability.Complexity.Problems.STCON.SubdivisionEndpoints
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Tactic.EncLen

/-!
# Initial data for the subdivided STCON seed search

The initializer returns the retained graph and seed-search parameters together with the
fixed source and target IDs. Both IDs are computed using the same chain bound as the
returned scan carrier. The setup uses logarithmic native workspace on the original input
and returns logarithmically many bits.

## Main results

* `Cslib.Complexity.STCON.length_configurationSubdivisionRequest_le`: for any valid scan
  IDs, the encoded request and its decoded coordinates charge the retained context and
  logarithmic overhead in the original input length.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open Reachability.Hoza Cslib.LayeredDigraph.Subdivision
open _root_.Turing.QueryMachine.Subdivision

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

/-- Convert a row-major original-source position to its offset-zero subdivision ID. -/
@[expose] def SeedSearchSetup.originalSourceID (s : SeedSearchSetup) (position : ℕ) : ℕ :=
  rootID position s.parameters.search.subdivision.chainBound

/-- Lookup uses linear native workspace in the encoded setup and binary source position. -/
theorem originalSourceID_inSpace :
    ComputableInSpace (fun p : SeedSearchSetup × ℕ => p.1.originalSourceID p.2)
      (encPair encSeedSearchSetup encNat) encNat
      (fun p => (encPair encSeedSearchSetup encNat p).length) := by
  have hsetup := fst encSeedSearchSetup encNat
  have hp := encSeedSearchSetup_parameters_budget hsetup
  have hs := encSeedSearchParameters_search_budget hp
  have hb := encSubdivisionSize_chainBound_budget (encSeedSearchSize_subdivision_budget hs)
  exact (budget_comp_linear rootID_inSpace
    (budget_prod (snd encSeedSearchSetup encNat) hb)).of_enc_eq fun p => by
      rw [SeedSearchSetup.originalSourceID]

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

/-- The initialized carrier count is the size of the codomain of `subdivisionIndex`
at the retained chain bound. -/
theorem configurationSeedSearchSetup_vertexCount (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    size.vertexCount = (((I.n - 1) + 1) * I.n) * (size.chainBound + 1) := by
  have h := subdivisionSize_vertexCount (configurationInstance ntm c w).n
    ((configurationInstance ntm c w).n - 1)
  rw [card_vertex, Nat.card_prod, Nat.card_fin, Nat.card_fin] at h
  exact h

/-- The row-major numbering with codomain the carrier size returned by the initializer. -/
noncomputable def configurationSubdivisionIndex (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    Vertex (Fin ((I.n - 1) + 1) × Fin I.n) size.chainBound ≃ Fin size.vertexCount :=
  (subdivisionIndex _ _).trans (finCongr (configurationSeedSearchSetup_vertexCount ntm c w).symm)

/-- The initialized numbering preserves the numeric ID of each row-major slot. -/
theorem configurationSubdivisionIndex_val (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ a : Vertex (Fin ((I.n - 1) + 1) × Fin I.n) size.chainBound,
      (configurationSubdivisionIndex ntm c w a).val = (subdivisionIndex I size.chainBound a).val :=
  fun _ => rfl

/-- The two fixed endpoint IDs are valid positions in the returned scan carrier. -/
theorem configurationSeedSearchSetup_endpoints_lt_vertexCount (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let s := configurationSeedSearchSetup ntm c w
    let n := s.parameters.search.subdivision.vertexCount
    s.sourceID < n ∧ s.targetID < n := by
  obtain ⟨hparams, hids⟩ := configurationSeedSearchSetup_endpoints ntm c w
  let I := configurationInstance ntm c w
  let bound := (configurationSeedSearchParameters ntm c w).search.subdivision.chainBound
  let index := subdivisionIndex I bound
  dsimp only
  rw [configurationSeedSearchSetup_vertexCount, hparams]
  rw [(Prod.mk.inj hids).1, (Prod.mk.inj hids).2]
  exact ⟨(index _).isLt, (index _).isLt⟩

/-- The retained source count is the size of the row-major original vertex carrier. -/
theorem configurationSeedSearchSetup_originalCount (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let s := configurationSeedSearchSetup ntm c w
    s.parameters.search.subdivision.originalCount = ((I.n - 1) + 1) * I.n := by
  obtain ⟨hparams, _⟩ := configurationSeedSearchSetup_endpoints ntm c w
  dsimp only at hparams ⊢
  rw [hparams]
  exact Nat.mul_comm _ _

/-- A source position in the initialized setup gives exactly the root used by the indexed
seed-search correctness theorem. -/
theorem configurationSeedSearchSetup_originalSourceID_eq (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let s := configurationSeedSearchSetup ntm c w
    let index := subdivisionIndex I s.parameters.search.subdivision.chainBound
    ∀ position : Fin (((I.n - 1) + 1) * I.n),
      s.originalSourceID position.val = (originalRootID index position).val := by
  dsimp only
  intro position
  rw [SeedSearchSetup.originalSourceID, originalRootID, subdivisionIndex_root_val,
    Equiv.apply_symm_apply]

/-- Every valid original-source position maps into the initialized subdivision carrier. -/
theorem configurationSeedSearchSetup_originalSourceID_lt_vertexCount
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let s := configurationSeedSearchSetup ntm c w
    ∀ {position : ℕ}, position < s.parameters.search.subdivision.originalCount →
      s.originalSourceID position < s.parameters.search.subdivision.vertexCount := by
  obtain ⟨hparams, _⟩ := configurationSeedSearchSetup_endpoints ntm c w
  dsimp only at hparams ⊢
  intro position hpos
  rw [hparams] at hpos
  rw [SeedSearchSetup.originalSourceID, hparams, rootID]
  let p := (configurationSeedSearchParameters ntm c w).search.subdivision
  change (p.chainBound + 1) * position < p.originalCount * (p.chainBound + 1)
  rw [Nat.mul_comm p.originalCount (p.chainBound + 1)]
  exact Nat.mul_lt_mul_of_pos_left hpos (Nat.succ_pos _)

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

/-- The retained subdivision parameters fit within the encoded seed-search setup. -/
theorem encSeedSearchSetup_subdivision_length_le (s : SeedSearchSetup) :
    (encSubdivisionSize s.parameters.search.subdivision).length ≤ (encSeedSearchSetup s).length :=
  (encSeedSearchSize_subdivision_length_le s.parameters.search).trans
    ((encSeedSearchParameters_search_length_le s.parameters).trans
      (encSeedSearchSetup_parameters_length_le s))

/-- The initialized subdivision has polynomially many vertices in the original input length. -/
theorem configurationSubdivisionVertexCount_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (fun w =>
      (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount) :=
  (configurationSeedSearchParameters_polyBounded ntm c).2.2.mono fun w => by
    simp only [(configurationSeedSearchSetup_endpoints ntm c w).1, le_refl]

/-- The subdivision vertex count has logarithmic binary length in the original word. -/
theorem length_configurationSubdivisionVertexCount_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      (encNat size.vertexCount).length ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, hsetup⟩ := length_configurationSeedSearchSetup_le_log ntm c
  refine ⟨C, fun w => ?_⟩
  let s := configurationSeedSearchSetup ntm c w
  exact (encSubdivisionSize_vertexCount_length_le s.parameters.search.subdivision).trans
    ((encSeedSearchSetup_subdivision_length_le s).trans (hsetup w))

/-- All valid requests to the initialized scan have logarithmic overhead over their explicitly
charged context. The same bound covers the decoded requests passed into the callback. -/
theorem length_configurationSubdivisionRequest_le {Context : Type}
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (encContext : Context ↪ List Bool) :
    ∃ C, ∀ (w : List Bool) (ctx : Context) (u v : ℕ),
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      u < size.vertexCount → v < size.vertexCount →
      let q : FlatQuery Context := ⟨ctx, size.chainBound, u, v⟩
      let budget := (encContext ctx).length + (Nat.log2 w.length + 1)
      (encFlatQuery encContext q).length ≤ C * budget ∧
        (encQuery encContext (decodeFlatQuery q)).length ≤ C * budget := by
  obtain ⟨K, hK⟩ := length_configurationSeedSearchSetup_le_log ntm c
  obtain ⟨D, hD⟩ := (decodeFlatQuery_inSpace encContext).length_le
  refine ⟨(D + 1) * (5 * K + 9), fun w ctx u v hu hv => ?_⟩
  let s := configurationSeedSearchSetup ntm c w
  let size := s.parameters.search.subdivision
  let q : FlatQuery Context := ⟨ctx, size.chainBound, u, v⟩
  let budget := (encContext ctx).length + (Nat.log2 w.length + 1)
  have hsize := encSeedSearchSetup_subdivision_length_le s
  have hb := (encSubdivisionSize_chainBound_length_le size).trans hsize
  have hvertex := (encSubdivisionSize_vertexCount_length_le size).trans hsize
  have hs := hK w
  have hq : (encFlatQuery encContext q).length ≤
      2 * (encContext ctx).length + 5 * (encSeedSearchSetup s).length + 6 := by
    have hfrom := (length_encNat_mono hu.le).trans hvertex
    have hto := (length_encNat_mono hv.le).trans hvertex
    enc_len [encFlatQuery_apply, encFlatQueryFields, q]
  have hbudget : (encFlatQuery encContext q).length + 1 ≤ (5 * K + 9) * budget := by
    calc
      _ ≤ 2 * (encContext ctx).length + 5 * (K * (Nat.log2 w.length + 1)) + 7 := by
        change (encSeedSearchSetup s).length ≤ _ at hs
        omega
      _ ≤ (5 * K + 9) * budget := by
        dsimp [budget]
        ring_nf
        omega
  have h := Nat.mul_le_mul_left (D + 1) hbudget
  rw [← Nat.mul_assoc] at h
  have hflat := (Nat.le_succ (encFlatQuery encContext q).length).trans
    (Nat.le_mul_of_pos_left _ (Nat.succ_pos D))
  exact ⟨hflat.trans h, (hD q).trans
    ((Nat.mul_le_mul_right _ (Nat.le_succ D)).trans h)⟩

end Cslib.Complexity.STCON
