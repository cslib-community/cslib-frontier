/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.SynchronousCorrelation
import CslibFrontier.Foundations.Quantum.POVM.Mixture
import CslibFrontier.Probability.PMF.Uniform

/-! # Synchronous rounding for a rectangular strategy with a randomized measurement -/

set_option linter.privateModule false

open Cslib.PCP Cslib.Quantum
open Cslib.Probability.PMF (uniformOfFintype)

private noncomputable def rectangular : QuantumStrategy Bool Bool Bool Bool Bool Unit where
  state := EuclideanSpace.single (false, ()) 1
  norm_state := by simp
  alice _ := POVM.mixture (uniformOfFintype Bool) fun b => POVM.const b
  bob y := POVM.const y

private noncomputable def marginal : PMF Bool := uniformOfFintype Bool
private noncomputable def independent : PMF (Bool × Bool) := uniformOfFintype (Bool × Bool)
private noncomputable def diagonal : PMF (Bool × Bool) := marginal.map fun x => (x, x)

private theorem diagonal_ne_independent : diagonal ≠ independent := by
  intro h
  have hs := Cslib.Probability.PMF.mem_support_uniformOfFintype (false, true)
    (α := Bool × Bool)
  change (false, true) ∈ independent.support at hs
  rw [← h, diagonal, PMF.support_map] at hs
  obtain ⟨x, _, hx⟩ := hs
  cases x <;> contradiction

/-- A single mixture approximates the rectangular strategy on both distinct couplings. -/
example :
    let δ := rectangular.synchronyDefect marginal
    ∃ (p : PMF {s : Finset (Unit × Bool) // s.Nonempty})
        (T : (s : {s : Finset (Unit × Bool) // s.Nonempty}) →
          QuantumStrategy Bool Bool Bool Bool s.val s.val),
      let error (μ : PMF (Bool × Bool)) := ∑ q, (μ q).toReal * ∑ a, ∑ b,
        |rectangular.prob q.1 q.2 a b - ∑ s, (p s).toReal * (T s).prob q.1 q.2 a b|
      let bound := 2 * √(2 * δ) + 4 * √(18 * δ + 20 * √δ)
      diagonal ≠ independent ∧
        (∀ s x a b, a ≠ b → (T s).prob x x a b = 0) ∧
        error diagonal ≤ bound ∧ error independent ≤ bound := by
  intro δ
  have hdiag_fst : diagonal.map Prod.fst = marginal := by
    rw [diagonal, PMF.map_comp]
    exact PMF.map_id marginal
  have hdiag_snd : diagonal.map Prod.snd = marginal := by
    rw [diagonal, PMF.map_comp]
    exact PMF.map_id marginal
  have hind_fst : independent.map Prod.fst = marginal :=
    Cslib.Probability.PMF.uniformOfFintype_prod_map_fst
  have hind_snd : independent.map Prod.snd = marginal :=
    Cslib.Probability.PMF.uniformOfFintype_prod_map_snd
  obtain ⟨p, T, _, _, hT, _, h⟩ := rectangular.exists_synchronous_correlation_mixture marginal
  exact ⟨p, T, diagonal_ne_independent, hT, h diagonal hdiag_fst hdiag_snd,
    h independent hind_fst hind_snd⟩
