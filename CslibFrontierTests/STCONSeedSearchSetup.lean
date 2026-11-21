/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SeedSearchSetup

/-! Ordinary-import checks for the original-input initializer and its scan endpoints. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSeedSearchSetup

open Cslib.Complexity.STCON Cslib.Reachability.Hoza
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Turing.QueryMachine.Subdivision

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

-- The fixed source can query any valid slot. Charging the setup as context gives a
-- logarithmic bound for the actual encoded pending callback state.
example :
    ∃ C, ∀ (w : List Bool) (v : ℕ),
      let s := configurationSeedSearchSetup ntm c w
      let size := s.parameters.search.subdivision
      v < size.vertexCount →
      let q : FlatQuery SeedSearchSetup := ⟨s, size.chainBound, s.sourceID, v⟩
      (encCallback encSeedSearchSetup encBool (flatCallbackStart q)).length ≤
        C * (Nat.log2 w.length + 1) := by
  obtain ⟨K, hK⟩ := length_configurationSeedSearchSetup_le_log ntm c
  obtain ⟨R, hR⟩ := length_configurationSubdivisionRequest_le ntm c encSeedSearchSetup
  obtain ⟨D, hD⟩ := (flatCallbackStart_inSpace encSeedSearchSetup encBool).length_le
  refine ⟨D * (R * (K + 1) + 1), fun w v hv => ?_⟩
  let s := configurationSeedSearchSetup ntm c w
  let q : FlatQuery SeedSearchSetup :=
    ⟨s, s.parameters.search.subdivision.chainBound, s.sourceID, v⟩
  let L := Nat.log2 w.length + 1
  have hsource := (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).1
  have hq := (hR w s s.sourceID v hsource hv).1
  have hctx : (encSeedSearchSetup s).length + L ≤ (K + 1) * L := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_right (hK w) L
  have hlen := hq.trans (Nat.mul_le_mul_left R hctx)
  rw [Nat.mul_assoc]
  refine (hD q).trans (Nat.mul_le_mul_left D ?_)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  exact Nat.add_le_add hlen (Nat.le_add_left _ _)

end CslibFrontierTests.STCONSeedSearchSetup
