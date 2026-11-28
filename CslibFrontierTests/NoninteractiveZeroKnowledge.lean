/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.NoninteractiveZeroKnowledge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-! # Checked instances of common-random-string proofs -/

set_option linter.privateModule false

namespace CslibFrontierTests.NoninteractiveZeroKnowledge

open Cslib.Complexity Turing.MultiTapeTM

private noncomputable def echoProtocol : CRSProtocol encBool where
  commonLength := 1
  proofLength := 1
  verify := Prod.fst
  computableInPolyTime_verify := ComputableInPolyTime.fst encBool encBits
  privateCoins := fun _ => 0
  respond := fun _ r _ => r

/-- The honest transcript retains the dependence between the common string and the proof. -/
example (a : Bool) {t : CRSTranscript} (h : t ∈ (echoProtocol.transcript a).support) :
    t.commonString = t.proof ∧ t.accepted = a := by
  rw [CRSProtocol.transcript, PMF.mem_support_bind_iff] at h
  obtain ⟨r, _, hr⟩ := h
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨coins, _, rfl⟩ := hr
  exact ⟨rfl, rfl⟩

example : {b : Bool | b = true} ∈ NISZK encBool := by
  apply NIPZK_subset_NISZK encBool
  apply BPP_subset_NIPZK encBool
  apply P_subset_BPP
  exact mem_P.mpr ⟨id, ComputableInPolyTime.id', fun _ => Iff.rfl⟩

end CslibFrontierTests.NoninteractiveZeroKnowledge
