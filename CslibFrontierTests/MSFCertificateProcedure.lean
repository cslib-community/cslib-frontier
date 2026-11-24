/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Procedure

/-!
# Tests for the certificate procedure as a program

A triangle on the vertices `0, 1, 2` with edges `0 = {0, 1}`, `1 = {1, 2}`, `2 = {0, 2}` and a
self-loop `3` at `2`, weighted by their index. The generic parts of Algorithm 1 are the trivial
ones: `γ = 1` (so the root, at level `1`, has `t = 1` block of one round and `r = 8`), every edge
scheduled in round `0`, the estimator answering *find* for every edge, and an exact minimum
spanning forest call answering `msf` at no comparison.

The structural fact checked is that the children are small (§3.6, p. 22): with `n = 3 < 4` the
child of the only round has no vertex, for every oracle.
-/

namespace CslibFrontierTests.MSFCertificateProcedure

open Cslib Cslib.Query Cslib.Query.Certificate Cslib.Multigraph Finset

/-- The ends of the four edges. -/
def ends : Fin 4 → Sym2 (Fin 3)
  | 0 => s(0, 1)
  | 1 => s(1, 2)
  | 2 => s(0, 2)
  | 3 => s(2, 2)

/-- Weights: the index of the edge. -/
def w : Fin 4 → ℕ := Fin.val

theorem levelT_pos (d : ℕ+) : 0 < levelT 1 d ^ 2 := by
  have := d.pos
  simp only [levelT, one_mul]
  positivity

/-- The trivial generic parts: every edge in round `0`, every estimate *find*, and `msf` as the
exact call. -/
noncomputable def cfg : Config (Fin 3) (Fin 4) where
  γ := 1
  sched inst _ := ⟨0, levelT_pos inst.level⟩
  est _ _ _ := pure fun _ => .find
  msfSub ends S := pure (msf ends w S)

/-- The root instance: all four edges on the three vertices. -/
abbrev root : Instance (Fin 3) (Fin 4) := Instance.root univ ends univ

theorem root_wellFormed : root.WellFormed :=
  Instance.wellFormed_root fun _ _ _ _ => mem_univ _

/-- The root has a single round. -/
theorem levelT_root : levelT cfg.γ root.level ^ 2 = 1 := by
  simp [cfg, levelT]

/-- **The children are small**: the child of the only round of the root has no vertex, since
`4 · #P ≤ n = 3`. This holds for every oracle. -/
theorem child_vertices_eq_empty (o : {ι : Type} → LEQuery (Fin 4) ι → ι) :
    (child cfg o root 0).vertices = ∅ := by
  have h := four_mul_sum_card_child_vertices_le cfg o root
  rw [levelT_root, sum_range_one] at h
  have h3 : #root.vertices = 3 := by simp
  exact card_eq_zero.1 (by omega)

end CslibFrontierTests.MSFCertificateProcedure
