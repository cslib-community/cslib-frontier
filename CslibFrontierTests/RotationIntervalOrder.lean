/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (rotation interval regression tests)

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CutInterval
import Mathlib.Logic.Equiv.Fin.Rotate

set_option linter.privateModule false

/-!
The interval API retains the original first-hit and port ranks without the loop realization
application. A four-dart rotation checks the cyclic laws and the effect of cutting an interval.
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

-- Swapping the two outgoing corners closes the first two darts into a separate orbit.
example :
    let split := r.rotate * Equiv.swap b (r.rotate.symm a)
    split.SameCycle a b ∧ ¬ split.SameCycle a c := by
  dsimp only
  have hproper : r.rotate b ≠ a := by decide
  rw [r.sameCycle_swap_cutInterval_iff a b rfl hproper a b,
    r.sameCycle_swap_cutInterval_iff a b rfl hproper a c,
    r.rotationDistance_self, ab_rank, ac_rank]
  decide

-- The first loop moves intact, and its last dart rotates back to its first dart in H.
example : ∃ (H : Graph) (E : Fin G.edges.length ≃ Fin H.edges.length) (s : RotationSystem H),
    H.vertices = [10, 9] ∧ Dart.vertex (E a.1, a.2) = 10 ∧ Dart.vertex (E b.1, b.2) = 10 ∧
      Dart.vertex (E c.1, c.2) = 9 ∧ s.rotate (E b.1, b.2) = (E a.1, a.2) ∧
      ¬s.rotate.SameCycle (E a.1, a.2) (E c.1, c.2) := by
  obtain ⟨H, E, s, hV, hEnds, hRotate⟩ :=
    r.exists_split_cutInterval a b rfl (by decide) 10 (by decide)
  have hA : Dart.vertex (G := H) (E a.1, a.2) = 10 := by
    rw [hEnds a, r.rotationDistance_self, ab_rank, ite_eq_left (by decide)]
  have hC : Dart.vertex (G := H) (E c.1, c.2) = 9 := by
    rw [hEnds c, ab_rank, ac_rank, ite_eq_right (by decide)]
    rfl
  refine ⟨H, E, s, hV, hA, ?_, hC, ?_, ?_⟩
  · rw [hEnds b, ite_eq_left ⟨rfl, le_rfl⟩]
  · let D : Dart G ≃ Dart H := Equiv.prodCongr E (Equiv.refl Bool)
    change s.rotate (D b) = D a
    change s.rotate = D.permCongr (r.rotate * Equiv.swap b (r.rotate.symm a)) at hRotate
    have hswap : (r.rotate * Equiv.swap b (r.rotate.symm a)) b = a := by decide
    rw [hRotate, Equiv.permCongr_apply, Equiv.symm_apply_apply, hswap]
  · rw [s.sameCycle_iff, hA, hC]
    decide

-- A singleton class and its three-dart complement cannot alternate.
example :
    ∃ lo hi : Dart G, lo.vertex = 9 ∧ hi.vertex = 9 ∧
      ((lo = a) ↔ (hi = a)) ∧
      ∀ d : Dart G, d.vertex = 9 →
        (((d = a) ↔ (lo = a)) ↔ r.rotationDistance lo d ≤ r.rotationDistance lo hi) := by
  let color (d : Dart G) := decide (d = a)
  obtain ⟨lo, hi, hlo, hhi, hcolor, hbetween⟩ :=
    r.exists_consecutive_class_of_no_alternates color ⟨a, rfl⟩ (by
      intro p q u v _ hpq huv hdiff hAlt
      by_cases hp : color p = true
      · exact hAlt.1 ((of_decide_eq_true hp).trans (of_decide_eq_true (hpq.symm.trans hp)).symm)
      · have hp' := Bool.eq_false_iff.mpr hp
        have hu := Bool.eq_true_of_not_eq_false (fun he => hdiff (hp'.trans he.symm))
        exact hAlt.2.1 ((of_decide_eq_true hu).trans (of_decide_eq_true (huv.symm.trans hu)).symm))
  have hlohi : r.portRank lo ≤ r.portRank hi := ((hbetween hi hhi).mp hcolor.symm).1
  refine ⟨lo, hi, hlo, hhi, ?_, ?_⟩
  · simpa only [color, decide_eq_decide] using hcolor
  · intro d hd
    have hdist := r.rotationDistance_le_iff_portRank_between lo hi d
      (hlo.trans hhi.symm) (hlo.trans hd.symm) hlohi
    simpa only [color, decide_eq_decide] using (hbetween d hd).trans hdist.symm

end CslibFrontierTests.RotationIntervalOrder
