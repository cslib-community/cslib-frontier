/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.HozaSize

/-! Checked clients for the seed-independent subdivision parameters. -/

set_option linter.privateModule false

namespace CslibFrontierTests.HozaSubdivisionSize

open Cslib.Reachability.Hoza Cslib.Code.JustesenFamily Cslib.LayeredDigraph.Subdivision
open Turing.MultiTapeTM

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

-- A scanner consumes the dimension through the existing row-major numbering.
example (w h : ℕ) :
    Vertex (Fin (h + 1) × Fin w) (subdivisionSize w h).chainBound ≃
      Fin (subdivisionSize w h).vertexCount :=
  let index := ((equivProd (Fin (h + 1) × Fin w) _).trans
    (finProdFinEquiv.prodCongr (Equiv.refl _))).trans finProdFinEquiv
  index.trans (finCongr (by simp only [subdivisionSize, Nat.mul_comm w (h + 1)]))

end CslibFrontierTests.HozaSubdivisionSize
