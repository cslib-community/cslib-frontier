/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.CommonNeighborAsymptotics
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A square-root planted-clique family

This ordinary-import client applies the native high-probability endpoint to the uniform
planted-set problem with target `min n ⌈√n⌉`. The minimum makes the family valid even at zero;
the target is at least `√n` from dimension one onward. It checks that a single fixed machine
handles an actual square-root-size family, with vanishing failure on the represented outputs.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedCliqueCommonNeighborAsymptotics

open Cslib Cslib.Probability Cslib.Probability.PlantedClique
open Cslib.Algorithms.PlantedClique Turing.MultiTapeTM Filter
open scoped Topology

private noncomputable def sqrtTarget (n : ℕ) : ℕ := min n ⌈Real.sqrt n⌉₊

example : ∃ s : ℕ,
    IsPPTOn encRecoveryInput (encList encUnary)
      (fun input => pure (commonNeighborRecover recoverInput s input)) ∧
    Tendsto (fun n =>
      (searchProblem (uniformPlantedSet n (sqrtTarget n) (Nat.min_le_left _ _))).experiment
        (fun G => PMF.pure (vertexSet n
          (commonNeighborRecover recoverInput s (RecoveryInput.ofGraph G (sqrtTarget n))))) false)
      atTop (𝓝 0) := by
  obtain ⟨s, hprogram, hsuccess⟩ :=
    exists_commonNeighborRecover_ppt_tendsto_failure (c := 1) (by norm_num)
  refine ⟨s, hprogram, hsuccess sqrtTarget
    (fun n => uniformPlantedSet n (sqrtTarget n) (Nat.min_le_left _ _)) ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [one_mul, sqrtTarget, Nat.cast_min]
  exact le_min (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hn)))
    (Nat.le_ceil (Real.sqrt n))

end CslibFrontierTests.PlantedCliqueCommonNeighborAsymptotics
