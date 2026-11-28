/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.HozaSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Foundations.Data.BitString.Binary

/-! Checked clients for the seed-independent subdivision parameters. -/

set_option linter.privateModule false

namespace CslibFrontierTests.HozaSubdivisionSize

open Cslib.Reachability.Hoza Cslib.Code.JustesenFamily Cslib.LayeredDigraph.Subdivision
open Cslib.BitString Turing.MultiTapeTM

example : ComputableInSpace (fun p : ℕ × ℕ => subdivisionSize p.1 p.2) (encPair encNat encNat)
    encSubdivisionSize (fun p => (encPair encNat encNat p).length) :=
  subdivisionSize_inSpace

-- The count is valid for one scan carrier shared by every candidate seed.
example (w h : ℕ) :
    let p := subdivisionSize w h
    (∀ (seed : Fin (codeLength w h) → Bool) (v : Fin (h + 1) × Fin w),
      generatedWeight seed v ≤ p.chainBound) ∧
    p.vertexCount = Nat.card (Vertex (Fin (h + 1) × Fin w) p.chainBound) := by
  exact ⟨fun seed v => (generatedWeight_lt_bound seed v).le, subdivisionSize_vertexCount w h⟩

example : ComputableInSpace (fun p : ℕ × ℕ => seedSearchSize p.1 p.2)
    (encPair encNat encNat) encSeedSearchSize (fun p => (encPair encNat encNat p).length) :=
  seedSearchSize_inSpace

-- The initializer supplies exactly the domain consumed by the ordered seed enumeration.
example (w h : ℕ) :
    Fin (seedSearchSize w h).seedLimit ≃ (Fin (seedSearchSize w h).seedWidth → Bool) :=
  (equivFin _).symm

-- The exclusive limit's additional bit is available in the retained binary count.
example (w h : ℕ) (rank : Fin (seedSearchSize w h).seedLimit) :
    (encNat rank.val).length ≤ (seedSearchSize w h).seedWidth ∧
      (encNat (seedSearchSize w h).seedLimit).length = (seedSearchSize w h).seedWidth + 1 :=
  ⟨length_encNat_le_of_lt_two_pow rank.isLt, length_seedSearchSize_seedLimit w h⟩

end CslibFrontierTests.HozaSubdivisionSize
