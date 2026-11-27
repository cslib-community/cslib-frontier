/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.MaxFlow.VertexSeparator
import CslibFrontier.Algorithms.Lean.IterativeCompression.OddCycleTransversal
import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal
meta import Mathlib.Combinatorics.SimpleGraph.Basic
meta import CslibFrontier.Algorithms.Lean.MaxFlow.VertexSeparator
meta import CslibFrontier.Algorithms.Lean.IterativeCompression.OddCycleTransversal
meta import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal

/-!
# Odd cycle transversal by iterative compression: tests

* The minimum vertex separator (`Cslib.Algorithms.Lean.MaxFlow.minSeparator`) on a path and on a
  four-cycle, with a forbidden vertex.
* Theorem-level facts, by `decide` on colourings and the correctness theorem `oct_isSome_iff`:
  the triangle and the five-cycle need exactly one deleted vertex, `K₄` needs exactly two, and
  the four-cycle is bipartite (`∅` suffices).
* Compiled runs of `oct` (`#guard`) on the same graphs, checking that each output is an odd cycle
  transversal of the right size with a colouring proper off it.
* Uniform `Basis.exact` Word-RAM execution and decision witnesses (`exists_oct_program`,
  `uniformDecidableInTime_oct`, `uniformDecidableInTimeLogWord_oct`) across empty, bipartite,
  odd-cycle, and `K₄` instances, including minimal word-width boundaries.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.OddCycleTransversal

open SimpleGraph Cslib.Algorithms.Lean.IterativeCompression Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.WordRAM.OddCycleTransversal Cslib.WordRAM

/-- The cycle on `Fin n`: `v` is adjacent to `v + 1 mod n`. -/
private def cyc (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.fromRel fun u v => (u.1 + 1) % n = v.1

private instance (n : ℕ) : DecidableRel (cyc n).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ((u.1 + 1) % n = v.1 ∨ (v.1 + 1) % n = u.1)))

/-- The path `0 - 1 - 2`. -/
private def path3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun u v => u.1 + 1 = v.1

private instance : DecidableRel path3.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1)))

/-- Boolean form of "`c` is proper off `S`", for compiled checks. -/
private def properOff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Vector Bool n)
    (S : List (Fin n)) : Bool :=
  decide (∀ u v : Fin n, G.Adj u v → u ∉ S → v ∉ S → vget c u ≠ vget c v)

/-- The output of `oct G k` is a solution: at most `k` vertices, no repetitions, and a colouring
proper off it (checked by `properOff`). -/
private def checkOct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Bool :=
  match oct G k with
  | some (S, c) => decide (S.length ≤ k) && decide S.Nodup && properOff G c S
  | none => false

/-! ### Minimum vertex separators -/

-- In the path `0 - 1 - 2`, one vertex separates `0` from `2`. A separator may contain terminals:
-- the cut nearest to the source returns `{0}`.
#guard (minSeparator path3 #v[false, false, false] #v[true, false, false]
  #v[false, false, true]).sep == [0]

-- In the four-cycle `0 - 1 - 2 - 3 - 0`, separating `{0, 1}` from `{2, 3}` needs two vertices
-- (the edges `0 - 3` and `1 - 2`).
#guard (minSeparator (cyc 4) #v[false, false, false, false] #v[true, true, false, false]
  #v[false, false, true, true]).sep.length == 2

-- With `1` forbidden as a separator vertex but blocking walks (in `Z`), one more vertex suffices.
#guard (minSeparator (cyc 4) #v[false, true, false, false] #v[true, true, false, false]
  #v[false, false, true, true]).sep.length == 1

-- If `Z` already separates, the separator is empty.
#guard (minSeparator (cyc 4) #v[true, true, false, false] #v[true, true, false, false]
  #v[false, false, true, true]).sep == []

/-! ### Theorem-level facts -/

/-- Two of any three vertices share a colour. -/
private theorem pigeon (c : Fin 3 → Bool) : ∃ u v : Fin 3, u ≠ v ∧ c u = c v := by
  revert c
  decide

/-- The triangle is not bipartite. -/
example : ¬ (⊤ : SimpleGraph (Fin 3)).IsOddCycleTransversal ∅ := by
  rw [isOddCycleTransversal_iff_exists_bool]
  rintro ⟨c, hc⟩
  obtain ⟨u, v, huv, h⟩ := pigeon c
  exact hc huv (Set.notMem_empty u) (Set.notMem_empty v) h

/-- Deleting one vertex of the triangle leaves an edge. -/
example : (⊤ : SimpleGraph (Fin 3)).IsOddCycleTransversal {0} := by
  rw [isOddCycleTransversal_iff_exists_bool]
  refine ⟨fun v => decide (v = 1), fun u v huv hu hv => ?_⟩
  simp only [Set.mem_singleton_iff] at hu hv
  revert u v
  decide

/-- The five-cycle is not bipartite: a proper colouring would alternate along an odd cycle. -/
private theorem cyc5_not_bipartite :
    ∀ c : Fin 5 → Bool, ∃ u v : Fin 5, (cyc 5).Adj u v ∧ c u = c v := by
  decide

/-- The five-cycle with vertex `0` deleted is a path. -/
private theorem cyc5_oct : (cyc 5).IsOddCycleTransversal ({0} : Finset (Fin 5)) := by
  rw [isOddCycleTransversal_iff_exists_bool]
  refine ⟨fun v => decide (v.1 % 2 = 1), fun u v huv hu hv => ?_⟩
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
  revert u v
  decide

/-- The four-cycle is bipartite. -/
private theorem cyc4_oct : (cyc 4).IsOddCycleTransversal ((∅ : Finset (Fin 4)) : Set (Fin 4)) := by
  rw [isOddCycleTransversal_iff_exists_bool]
  refine ⟨fun v => decide (v.1 % 2 = 1), fun u v huv _ _ => ?_⟩
  revert u v
  decide

example : (cyc 4).IsBipartite := by
  have := cyc4_oct
  rwa [Finset.coe_empty, isOddCycleTransversal_empty_iff] at this

/-- Any three of the four vertices of `K₄`, avoiding one deleted vertex, contain two of the same
colour. -/
private theorem k4_pigeon :
    ∀ a : Fin 4, ∀ c : Fin 4 → Bool, ∃ u v : Fin 4, u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ c u = c v := by
  decide

/-- `K₄` has no odd cycle transversal of at most one vertex. -/
private theorem k4_no_small_oct (T : Finset (Fin 4)) (hT : T.card ≤ 1) :
    ¬ (⊤ : SimpleGraph (Fin 4)).IsOddCycleTransversal T := by
  obtain ⟨a, ha⟩ : ∃ a, T ⊆ {a} := by
    rcases Finset.card_le_one_iff_subset_singleton.mp hT with ⟨a, ha⟩
    exact ⟨a, ha⟩
  rw [isOddCycleTransversal_iff_exists_bool]
  rintro ⟨c, hc⟩
  obtain ⟨u, v, huv, hua, hva, h⟩ := k4_pigeon a c
  exact hc huv (fun hu => hua (Finset.mem_singleton.mp (ha hu)))
    (fun hv => hva (Finset.mem_singleton.mp (ha hv))) h

/-- Deleting two vertices of `K₄` leaves an edge. -/
private theorem k4_oct :
    (⊤ : SimpleGraph (Fin 4)).IsOddCycleTransversal ({0, 1} : Finset (Fin 4)) := by
  rw [isOddCycleTransversal_iff_exists_bool]
  refine ⟨fun v => decide (v = 2), fun u v huv hu hv => ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hu hv
  revert u v
  decide

/-- `oct` on `K₄`: no solution with one vertex, a solution with two. -/
example : oct (⊤ : SimpleGraph (Fin 4)) 1 = none ∧
    (oct (⊤ : SimpleGraph (Fin 4)) 2).isSome := by
  refine ⟨Option.not_isSome_iff_eq_none.mp fun h => ?_,
    oct_isSome_iff.mpr ⟨_, k4_oct, by decide⟩⟩
  obtain ⟨T, hT, hk⟩ := oct_isSome_iff.mp h
  exact k4_no_small_oct T hk hT

/-- `oct` on the five-cycle: no solution with no vertex, a solution with one. -/
example : oct (cyc 5) 0 = none ∧ (oct (cyc 5) 1).isSome := by
  refine ⟨Option.not_isSome_iff_eq_none.mp fun h => ?_,
    oct_isSome_iff.mpr ⟨_, cyc5_oct, by decide⟩⟩
  obtain ⟨T, hT, hk⟩ := oct_isSome_iff.mp h
  obtain rfl := Finset.card_eq_zero.mp (Nat.le_zero.mp hk)
  rw [isOddCycleTransversal_iff_exists_bool] at hT
  obtain ⟨c, hc⟩ := hT
  obtain ⟨u, v, huv, h⟩ := cyc5_not_bipartite c
  exact hc huv (by simp) (by simp) h

/-- `oct` on the four-cycle with `k = 0` succeeds. -/
example : (oct (cyc 4) 0).isSome :=
  oct_isSome_iff.mpr ⟨∅, cyc4_oct, le_rfl⟩

/-! ### Compiled runs -/

-- The triangle: one vertex.
#guard (oct (⊤ : SimpleGraph (Fin 3)) 0).isNone
#guard checkOct (⊤ : SimpleGraph (Fin 3)) 1

-- The five-cycle: one vertex. With `k = 3` the output need not be minimum (here it has three
-- vertices): `oct` decides "at most `k`".
#guard (oct (cyc 5) 0).isNone
#guard checkOct (cyc 5) 1
#guard checkOct (cyc 5) 3

-- `K₄`: two vertices.
#guard (oct (⊤ : SimpleGraph (Fin 4)) 1).isNone
#guard checkOct (⊤ : SimpleGraph (Fin 4)) 2

-- The four-cycle and the path are bipartite: no vertex.
#guard checkOct (cyc 4) 0
#guard checkOct path3 0

-- Two disjoint triangles in `Fin 6` need two vertices.
private def twoTriangles : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v => u.1 / 3 = v.1 / 3

private instance : DecidableRel twoTriangles.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (u.1 / 3 = v.1 / 3 ∨ v.1 / 3 = u.1 / 3)))

#guard (oct twoTriangles 1).isNone
#guard checkOct twoTriangles 2

-- The seven-cycle: one vertex.
#guard (oct (cyc 7) 0).isNone
#guard checkOct (cyc 7) 1

/-! ### Word-RAM input encoding and execution witnesses -/

#guard encodeInput (⊥ : SimpleGraph (Fin 0)) 0 == [0, 0]
#guard octWorkspace 0 == 11
#guard (encodeInput path3 0).length == 11
#guard octWorkspace 4 == 175
#guard octWorkspace 5 == 241

/-- Empty graph `Fin 0` with `k = 0` at minimal word width `w = 4` (`octWorkspace 0 = 11 < 2 ^ 4`):
halts with `1` within `C` instructions. -/
example :
    ∃ r C pc : ℕ, 0 < C ∧ ∃ (prog : Program .exact r) (y : Data r) (steps : ℕ),
      Runs 4 prog (State.init (encodeInput (⊥ : SimpleGraph (Fin 0)) 0)) ⟨pc, y⟩ steps ∧
      step 4 prog ⟨pc, y⟩ = .halt 1 ∧
      steps + 1 ≤ C := by
  obtain ⟨r, C, pc, hC, prog, hprog⟩ := exists_oct_program
  obtain ⟨y, steps, res, hruns, hhalt, htime, _, _, hyes, _⟩ :=
    hprog (⊥ : SimpleGraph (Fin 0)) 0 4 (by decide) (by decide)
  have hres1 : res = 1 :=
    hyes.mpr ⟨∅, isOddCycleTransversal_iff_exists_bool.mpr ⟨Fin.elim0, fun {u} => u.elim0⟩,
      Nat.zero_le 0⟩
  subst hres1
  exact ⟨r, C, pc, hC, prog, y, steps, hruns, hhalt, by simpa using htime⟩

/-- Five-cycle at word width `w = 8` (`octWorkspace 5 = 241 < 2 ^ 8`): rejects `k = 0` (`halt 0`)
and accepts `k = 1` (`halt 1`), materializing a valid 1-vertex odd cycle transversal and proper
2-colouring in machine memory. -/
example :
    ∃ r C pc : ℕ, 0 < C ∧ ∃ prog : Program .exact r,
      (∃ (y₀ : Data r) (s₀ : ℕ),
        Runs 8 prog (State.init (encodeInput (cyc 5) 0)) ⟨pc, y₀⟩ s₀ ∧
        step 8 prog ⟨pc, y₀⟩ = .halt 0 ∧
        s₀ + 1 ≤ C * 6 ^ 5) ∧
      (∃ (y₁ : Data r) (s₁ : ℕ),
        Runs 8 prog (State.init (encodeInput (cyc 5) 1)) ⟨pc, y₁⟩ s₁ ∧
        step 8 prog ⟨pc, y₁⟩ = .halt 1 ∧
        s₁ + 1 ≤ C * 3 * 6 ^ 5 ∧
        let S : Finset (Fin 5) := Finset.univ.filter fun v => y₁.mem (sepAddr 5 v.1) = 1
        (cyc 5).IsOddCycleTransversal (S : Set (Fin 5)) ∧ S.card ≤ 1) := by
  obtain ⟨r, C, pc, hC, prog, hprog⟩ := exists_oct_program
  obtain ⟨y₀, s₀, r₀, hrun₀, hhalt₀, htime₀, hle₀, his₀, _, _⟩ :=
    hprog (cyc 5) 0 8 (by decide) (by decide)
  have hr₀ : r₀ = 0 := by
    by_cases h1 : r₀ = 1
    · obtain ⟨T, hT, hk⟩ := oct_isSome_iff.mp (his₀.mp h1)
      obtain rfl := Finset.card_eq_zero.mp (Nat.le_zero.mp hk)
      obtain ⟨c, hc⟩ := isOddCycleTransversal_iff_exists_bool.mp hT
      obtain ⟨u, v, huv, heq⟩ := cyc5_not_bipartite c
      exact absurd heq (hc huv (by simp) (by simp))
    · omega
  subst hr₀
  obtain ⟨y₁, s₁, r₁, hrun₁, hhalt₁, htime₁, _, _, hyes₁, hmem₁⟩ :=
    hprog (cyc 5) 1 8 (by decide) (by decide)
  have hr₁ : r₁ = 1 := hyes₁.mpr ⟨{0}, cyc5_oct, by decide⟩
  subst hr₁
  obtain ⟨_, hoct₁, hcard₁, _⟩ := hmem₁ rfl
  exact ⟨r, C, pc, hC, prog,
    ⟨y₀, s₀, hrun₀, hhalt₀, by simpa using htime₀⟩,
    ⟨y₁, s₁, hrun₁, hhalt₁, by simpa using htime₁, hoct₁, hcard₁⟩⟩

/-- `K₄` width-invariance check (`w = 8` and `w = 32`): rejects `k = 1` and accepts `k = 2` at
both widths with the same uniform program. -/
example :
    ∃ r C pc : ℕ, 0 < C ∧ ∃ prog : Program .exact r,
      ∀ w ∈ ([8, 32] : List ℕ),
        (∃ y₁ s₁,
          Runs w prog (State.init (encodeInput (⊤ : SimpleGraph (Fin 4)) 1)) ⟨pc, y₁⟩ s₁ ∧
          step w prog ⟨pc, y₁⟩ = .halt 0 ∧
          s₁ + 1 ≤ C * 3 * 5 ^ 5) ∧
        (∃ y₂ s₂,
          Runs w prog (State.init (encodeInput (⊤ : SimpleGraph (Fin 4)) 2)) ⟨pc, y₂⟩ s₂ ∧
          step w prog ⟨pc, y₂⟩ = .halt 1 ∧
          s₂ + 1 ≤ C * 9 * 5 ^ 5) := by
  obtain ⟨r, C, pc, hC, prog, hprog⟩ := exists_oct_program
  refine ⟨r, C, pc, hC, prog, fun w hw => ?_⟩
  have hw_ws : Fits w (octWorkspace 4) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> decide
  have hw_2 : Fits w 2 := hw_ws.of_le (by decide)
  have hw_1 : Fits w 1 := hw_ws.of_le (by decide)
  obtain ⟨y₁, s₁, r₁, hrun₁, hhalt₁, htime₁, hle₁, _, hyes₁, _⟩ :=
    hprog (⊤ : SimpleGraph (Fin 4)) 1 w hw_ws hw_1
  have hr₁ : r₁ = 0 := by
    by_cases h1 : r₁ = 1
    · obtain ⟨T, hT, hk⟩ := hyes₁.mp h1
      exact absurd hT (k4_no_small_oct T hk)
    · omega
  subst hr₁
  obtain ⟨y₂, s₂, r₂, hrun₂, hhalt₂, htime₂, _, _, hyes₂, _⟩ :=
    hprog (⊤ : SimpleGraph (Fin 4)) 2 w hw_ws hw_2
  have hr₂ : r₂ = 1 := hyes₂.mpr ⟨{0, 1}, k4_oct, by decide⟩
  subst hr₂
  exact ⟨⟨y₁, s₁, hrun₁, hhalt₁, by simpa using htime₁⟩,
    ⟨y₂, s₂, hrun₂, hhalt₂, by simpa using htime₂⟩⟩

/-- Packaged `UniformDecidableInTime` and `UniformDecidableInTimeLogWord` witnesses. -/
example :
    (∃ C : ℕ, 0 < C ∧
      UniformDecidableInTime .exact OctInstance.Yes
        (fun _ => OctInstance.encode)
        (fun x _ => C * 3 ^ x.k * (x.n + 1) ^ 5)
        (fun x w => Fits w (octWorkspace x.n))) ∧
    (∃ C : ℕ, 0 < C ∧
      UniformDecidableInTimeLogWord .exact OctInstance.Yes
        (fun _ => OctInstance.encode)
        (fun x => x.encode.length)
        (fun x _ => C * 3 ^ x.k * (x.n + 1) ^ 5)) :=
  ⟨uniformDecidableInTime_oct, uniformDecidableInTimeLogWord_oct⟩

end CslibFrontierTests.OddCycleTransversal
