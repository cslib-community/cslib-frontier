/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler.Correct

/-! Ordinary-import checks for the original-input initializer and its scan sources. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSeedSearchSetup

open Cslib.Complexity.STCON Cslib.Reachability.Hoza
open Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)

example :
    ComputableInLogSpace (configurationSeedSearchSetup ntm c) encBits encSeedSearchSetup ∧
    ∃ C, ∀ w : List Bool,
      (encSeedSearchSetup (configurationSeedSearchSetup ntm c w)).length ≤
        C * (Nat.log2 w.length + 1) :=
  ⟨configurationSeedSearchSetup_inLogSpace ntm c, length_configurationSeedSearchSetup_le_log ntm c⟩

-- Both scalar endpoints can be used directly as bounded scan positions.
example (w : List Bool) :
    let s := configurationSeedSearchSetup ntm c w
    let n := s.parameters.search.subdivision.vertexCount
    s.sourceID < n ∧ s.targetID < n :=
  configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w

-- The indexed loop can compute the next source from the setup it already retains.
example :
    ComputableInSpace (fun p : SeedSearchSetup × ℕ => p.1.originalSourceID p.2)
      (encPair encSeedSearchSetup encNat) encNat
      (fun p => (encPair encSeedSearchSetup encNat p).length) :=
  originalSourceID_inSpace

example (w : List Bool) :
    let I := configurationInstance ntm c w
    let s := configurationSeedSearchSetup ntm c w
    let index := subdivisionIndex I s.parameters.search.subdivision.chainBound
    s.parameters.search.subdivision.originalCount = ((I.n - 1) + 1) * I.n ∧
    ∀ position : Fin (((I.n - 1) + 1) * I.n),
      s.originalSourceID position.val = (originalRootID index position).val :=
  ⟨configurationSeedSearchSetup_originalCount ntm c w,
    configurationSeedSearchSetup_originalSourceID_eq ntm c w⟩

example (w : List Bool) :
    let s := configurationSeedSearchSetup ntm c w
    ∀ {position : ℕ}, position < s.parameters.search.subdivision.originalCount →
      s.originalSourceID position < s.parameters.search.subdivision.vertexCount :=
  configurationSeedSearchSetup_originalSourceID_lt_vertexCount ntm c w

open Cslib.Complexity Cslib.DoubleCounting Cslib.Code.JustesenFamily in
-- Exact scanner outcomes give one scheduler outcome, including for a rejecting input.
example (input : List Bool)
    (hspace : ntm.RunsInSpace input (c * (Nat.log2 input.length + 1))) :
    let setup := configurationSeedSearchSetup ntm c input
    let hs := (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c input).1
    let hr := fun _ hp =>
      configurationSeedSearchSetup_originalSourceID_lt_vertexCount ntm c input hp
    ∃ (scan : SeedScanRequest → List (Option ControllerVerdict)), ∃ result,
      runSeedSchedulerFor setup hs hr (fun frame => scan frame.request) = [some result] ∧
      (result.reachable = true ↔ ntm.Accepts input) := by
  classical
  intro setup hs hr
  let I := configurationInstance ntm c input
  let index := configurationSubdivisionIndex ntm c input
  let target : Fin setup.parameters.search.subdivision.vertexCount :=
    ⟨setup.targetID, (configurationSeedSearchSetup_endpoints_lt_vertexCount
      ntm c input).2⟩
  let adj (rank : ℕ) := generatedSubdivisionAdj (layeredDigraph I) index
    (fun j : Fin (codeLength I.n (I.n - 1)) => rank.testBit j.val)
  let edge (rank : ℕ) (u v : Fin setup.parameters.search.subdivision.vertexCount) : List Bool :=
    pure (by classical exact decide (adj rank u v))
  let member (rank : ℕ) (source : Fin setup.parameters.search.subdivision.vertexCount) :
      MembershipScan List setup.parameters.search.subdivision.vertexCount :=
    fun radius _ v => pure (by classical exact decide (v ∈ round (adj rank) source radius))
  let scan (request : SeedScanRequest) : List (Option ControllerVerdict) :=
    if h : request.sourceID < setup.parameters.search.subdivision.vertexCount then
      runController (edge request.seed) (member request.seed ⟨request.sourceID, h⟩) target
    else []
  obtain ⟨result, hresult, _, _, hreach⟩ :=
    configurationSeedScheduler_correct ntm c input scan (by
      intro seed source
      obtain ⟨verdict, hrun, hspec⟩ := runController_correct (m := List)
        (r := adj seed.val) (s := source) (target := target)
        (edge := edge seed.val) (member := member seed.val source)
        (fun u v => by
          change pure (decide (adj seed.val u v)) = _
          congr 1
          simp only [decide_eq_decide])
        (fun radius _ v => by
          change pure (decide (v ∈ round (adj seed.val) source radius)) = _
          congr 1)
      refine ⟨verdict, ?_, ?_⟩
      · change scan ⟨setup, seed.val, source.val⟩ = _
        exact (dite_eq_left source.isLt).trans hrun
      · cases verdict with
        | bad j => exact hspec.2
        | decided hit => exact hspec)
  exact ⟨scan, result, hresult, hreach.trans (configurationInstance_mem_iff ntm c hspace)⟩

end CslibFrontierTests.STCONSeedSearchSetup
