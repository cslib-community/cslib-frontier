/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Iterate

/-! Tests of cuts, as a client that sees only the public statements.

* The program that returns its instance as the only piece is a cut, so `Cut.IsCut` is
  satisfiable, and composing it with itself is a cut again by `Cut.IsCut.comp`.
* The cut that `Cut.OneCutAt.exists_isCut` gives is a program for the cut hypothesis
  `Interpreter.CutProg`, by `Cut.IsCut.cutProg`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationCuts

open Cslib.Circuits.Arithmetic.Separation.Interpreter Cslib.Circuits.Arithmetic.Separation.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- The program that returns the list of its argument alone. -/
def single : Fm := .cons .id (.quote .nil)

/-- It is a cut into one piece, which does not change steps or sizes. -/
theorem isCut_single (τ s : ℕ) : IsCut θ τ s τ s 1 3 single.code := by
  intro z hz
  refine ⟨[(1, .cons z .nil)], ?_, ?_, fun hp => ⟨?_, ?_⟩⟩
  · rw [Fm.ofTree_code]
    exact (Gives.id z).cons (Gives.quote .nil z)
  · simpa [Tree.toList] using hz
  · simpa [Tree.toList] using hp
  · simp [wsum, pvProd, Tree.toList]

/-- Twice the same cut: one piece again, in the time of `Cut.IsCut.comp`. -/
example (τ s : ℕ) :
    IsCut θ τ s τ s 1 (3 + 1 * (3 + 62 * 1 + 110) + 100) (cutComp single.code single.code).code :=
  (isCut_single τ s).comp (isCut_single τ s)

/-- A cut with weaker bounds. -/
example (τ s : ℕ) : IsCut θ τ s (τ + 1) (2 * s) 5 10 single.code :=
  (isCut_single τ s).mono (Nat.le_succ τ) (by omega) (by omega) (by omega)

/-- From one cut by any factor to a program for the cut hypothesis. -/
example {v a₀ α H Λ τ s : ℕ} (hc : OneCutAt θ v a₀ α Λ) (hv : 110 ≤ v) (hΛ : 2 ≤ Λ)
    (hloss : (8 * Λ ^ 2) ^ (α + 1) ≤ v) (hH : a₀ + 4 ≤ H) (hH' : 200 ≤ H) (hτ : v ^ H ≤ τ)
    (hτα : τ ≤ v ^ α) (hs : s * v ^ 48 ≤ τ) : ∃ G, CutProg θ H v τ s G :=
  let ⟨G, hG, hcut⟩ := hc.exists_isCut hv hΛ hloss hH hH' hτ hτα hs
  ⟨G, hcut.cutProg hG (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)⟩

end CslibFrontierTests.SeparationCuts
