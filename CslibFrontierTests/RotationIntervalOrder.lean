/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder

/-!
The generic interval topic alone exposes the original first-hit and port-rank API,
without the loop realization application. Concrete four-dart intervals check the new
anchor and cyclic laws in both directions.
-/

namespace CslibFrontierTests.RotationIntervalOrder

open Cslib.Complexity Cslib.Complexity.Graph

private abbrev G : Graph := ⟨[9], [(9, 9), (9, 9)]⟩

private def r : RotationSystem G where
  rotate := ((Dart.indexEquiv G).trans (finRotate 4)).trans (Dart.indexEquiv G).symm
  sameCycle_iff := by decide

private abbrev a : Dart G := (0, false)
private abbrev b : Dart G := (0, true)
private abbrev c : Dart G := (1, false)

private theorem ab_rank : r.rotationDistance a b = 1 := by
  apply r.rotationDistance_eq a b rfl 1 (by decide)
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  decide

private theorem ac_rank : r.rotationDistance a c = 2 := by
  apply r.rotationDistance_eq a c rfl 2 (by decide)
  intro k hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl <;> decide

private theorem interval : b ∈ r.rotationInterval a c := by
  apply (r.mem_rotationInterval_iff_lt_distance a b c rfl rfl (by decide)
    (by decide) (by decide)).mpr
  rw [ab_rank, ac_rank]
  decide

example : c ∈ r.rotationInterval b a :=
  (r.mem_rotationInterval_cyclic a b c rfl rfl (by decide) (by decide) (by decide)).mp interval

example : ¬c ∈ r.rotationInterval a b := by
  rw [r.mem_rotationInterval_iff_lt_distance a c b rfl rfl (by decide)
    (by decide) (by decide), ac_rank, ab_rank]
  decide

-- Original QNs and types remain directly usable from the lower topic.
example : r.rotationDistance a a = 0 := r.rotationDistance_self a

example : r.portRank a ≠ r.portRank b :=
  fun h => (by decide : a ≠ b) (r.portRank_injective a b rfl h)

-- A singleton class and its three-dart complement cannot alternate.
example :
    ∃ lo hi : Dart G, lo.vertex = 9 ∧ hi.vertex = 9 ∧
      ((lo = a) ↔ (hi = a)) ∧
      ∀ d : Dart G, d.vertex = 9 →
        (((d = a) ↔ (lo = a)) ↔ r.portRank lo ≤ r.portRank d ∧ r.portRank d ≤ r.portRank hi) := by
  let color (d : Dart G) := decide (d = a)
  suffices h : ∃ lo hi : Dart G, lo.vertex = 9 ∧ hi.vertex = 9 ∧ color lo = color hi ∧
      ∀ d : Dart G, d.vertex = 9 →
        (color d = color lo ↔ r.portRank lo ≤ r.portRank d ∧ r.portRank d ≤ r.portRank hi) by
    simpa only [color, decide_eq_decide] using h
  apply r.exists_consecutive_class_of_no_alternates color ⟨a, rfl⟩
  intro p q u v _ hpq huv hdiff hAlt
  by_cases hp : color p = true
  · exact hAlt.1 ((of_decide_eq_true hp).trans (of_decide_eq_true (hpq.symm.trans hp)).symm)
  · have hp' := Bool.eq_false_iff.mpr hp
    have hu := Bool.eq_true_of_not_eq_false (fun he => hdiff (hp'.trans he.symm))
    exact hAlt.2.1 ((of_decide_eq_true hu).trans (of_decide_eq_true (huv.symm.trans hu)).symm)

end CslibFrontierTests.RotationIntervalOrder
