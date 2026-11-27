/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Combinatorics.Expander.Connected

/-!
# Spectral gap from one self-loop, and pointwise mixing (Arora–Barak draft, 7.28 and 7.30)

The hypotheses of `Cslib.RotationMap.spectralExpansion_le_one_sub_of_preconnected_of_loop`
(Lemma 7.28) and `Cslib.RotationMap.card_pow_lt_two_mul_card_mul_card_filter_neighbor_pow_eq`
(Corollary 7.30) are satisfiable: the single edge on two vertices with one self-loop at each vertex
is connected and looped, so both apply to it. Corollary 7.30 also applies to a disconnected graph,
three isolated vertices with a self-loop each, where it is about the component of the start vertex.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ExpanderPointwiseMixing

open Cslib Cslib.RotationMap Finset

/-- The edge between the two vertices of `Bool`, with a self-loop at each vertex. -/
def edgeWithLoops : RotationMap Bool (Unit ⊕ Unit) :=
  (ofInvolutive (!·) fun b ↦ Bool.not_not b).addLoops Unit

theorem edgeWithLoops_loop (v : Bool) : ∃ i, edgeWithLoops.neighbor v i = v :=
  ⟨.inr (), rfl⟩

theorem edgeWithLoops_preconnected : edgeWithLoops.toSimpleGraph.Preconnected := by
  have h : edgeWithLoops.toSimpleGraph.Adj false true := ⟨by decide, .inl (), rfl⟩
  intro u v
  cases u <;> cases v
  exacts [.refl _, h.reachable, h.symm.reachable, .refl _]

-- Lemma 7.28 for the looped edge: `λ ≤ 1 - 1 / (8 · 2 · 2³)`.
example : edgeWithLoops.spectralExpansion ≤ 1 - 1 / (8 * 2 * 2 ^ 3) := by
  have h := edgeWithLoops.spectralExpansion_le_one_sub_of_preconnected_of_loop edgeWithLoops_loop
    edgeWithLoops_preconnected
  simpa using h

-- Corollary 7.30 for the looped edge, with `T = 160 ≥ 10 · 2 · 2³ · log 2`.
example : Fintype.card (Unit ⊕ Unit) ^ 160 < 2 * Fintype.card Bool *
    #{k : Fin 160 → Unit ⊕ Unit | (edgeWithLoops.pow 160).neighbor false k = true} :=
  edgeWithLoops.card_pow_lt_two_mul_card_mul_card_filter_neighbor_pow_eq edgeWithLoops_loop
    (edgeWithLoops_preconnected false true) (by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_bool]
      push_cast
      nlinarith)

-- Corollary 7.30 on three isolated looped vertices, with `T = 540 ≥ 10 · 1 · 3³ · log 3`.
example : Fintype.card Unit ^ 540 < 2 * Fintype.card (Fin 3) *
    #{k : Fin 540 → Unit | ((loops (Fin 3) Unit).pow 540).neighbor 0 k = 0} :=
  (loops (Fin 3) Unit).card_pow_lt_two_mul_card_mul_card_filter_neighbor_pow_eq
    (fun _ ↦ ⟨(), rfl⟩) (.refl 0) (by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      simp only [Fintype.card_unit, Fintype.card_fin]
      push_cast
      nlinarith)

end CslibFrontierTests.ExpanderPointwiseMixing
