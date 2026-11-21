/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.Uniform

/-!
# Prediction after a uniform additive offset

Changing variables from the offset to the first masked digest gives a uniform digest independent
of the key. A correct masked prediction for a distinct message then gives a correct prediction of
the difference between the original digests. These identities are shared by the one-time
Carter–Wegman experiment and pairwise unpredictability.
-/

public section

namespace Cslib.Probability

open scoped ENNReal

/-- With the offset recovered from the first shifted digest, a second shifted digest equals the
prediction exactly when the original digests have the predicted difference. -/
theorem add_recovered_offset_eq_iff {Y : Type*} [AddGroup Y] (first second t t' : Y) :
    second + (-first + t) = t' ↔ second - first = t' - t := by
  rw [← add_assoc, ← sub_eq_add_neg, eq_sub_iff_add_eq.symm]

namespace IsDeltaUniversalHash

variable {K M Y : Type*} [AddGroup Y] [DecidableEq M] [DecidableEq Y]
  {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}

/-- A fixed prediction after seeing a masked digest succeeds for a distinct message only when the
original digests have the predicted difference. The key may have any distribution. -/
theorem bind_recovered_offset_le (h : IsDeltaUniversalHash seed hash ε)
    (m m' : M) (t t' : Y) :
    (seed.bind fun k =>
      PMF.pure (decide (m' ≠ m) && decide (hash k m' + (-hash k m + t) = t'))) true ≤ ε := by
  by_cases hne : m' = m
  · simp [hne]
  · have heq (k : K) :
        (decide (m' ≠ m) && decide (hash k m' + (-hash k m + t) = t')) =
          decide (hash k m' - hash k m = t' - t) := by
      rw [show decide (m' ≠ m) = true from decide_eq_true hne, Bool.true_and]
      exact Bool.decide_congr (add_recovered_offset_eq_iff (hash k m) (hash k m') t t')
    simp_rw [heq]
    rw [PMF.bind_pure_decide_apply_true]
    exact h m' m hne (t' - t)

/-- After seeing the first digest masked by a private uniform offset, an adaptive prediction for
a distinct message succeeds with probability at most the original difference-universality bound.
The response may retain arbitrary data in its outcome. -/
theorem bind_uniform_offset_le {A : Type*} [Fintype Y] (h : IsDeltaUniversalHash seed hash ε)
    (m : M) (respond : Y → PMF A) (message : A → M) (digest : A → Y) :
    (seed.bind fun k =>
      (PMF.uniformOfFintype Y).bind fun offset =>
        (respond (hash k m + offset)).bind fun guess =>
          PMF.pure (decide (message guess ≠ m) &&
            decide (hash k (message guess) + offset = digest guess))) true ≤ ε := by
  have hreparam (k : K) := PMF.uniformOfFintype_bind_add_offset (hash k m) fun t offset =>
    (respond t).bind fun guess =>
      PMF.pure (decide (message guess ≠ m) &&
        decide (hash k (message guess) + offset = digest guess))
  simp_rw [hreparam]
  rw [PMF.bind_comm]
  refine PMF.bind_apply_le_on_support _ fun t _ => ?_
  rw [PMF.bind_comm]
  exact PMF.bind_apply_le_on_support _ fun guess _ =>
    h.bind_recovered_offset_le m (message guess) t (digest guess)

end IsDeltaUniversalHash

end Cslib.Probability
