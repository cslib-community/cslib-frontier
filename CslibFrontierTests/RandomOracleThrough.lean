/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test suite)

import CslibFrontier.Languages.Probabilistic.RandomOracle.Through
import CslibFrontier.Probability.PMF.Uniform

/-!
# Tests for `CslibFrontier.Languages.Probabilistic.RandomOracle.Through`

`HasImageCollision` on concrete caches, and `closeTo_runWith_memoize_simulate_query` at an
injective map (the error is zero) and at a constant map (the error cannot be dropped).
-/

set_option linter.privateModule false

namespace Cslib.RandomOracle

open Probability

/-- An injective map has no image collision on any cache. -/
private theorem not_hasImageCollision_of_injective {M Y Z : Type} {φ : M → Y}
    (hφ : Function.Injective φ) (cache : List (M × Z)) : ¬ HasImageCollision φ cache :=
  fun ⟨_, _, _, _, hne, h⟩ => hne (hφ h)

/-- Two distinct cached queries with the same image form a `HasImageCollision`. -/
example (z z' : ℕ) : HasImageCollision (fun _ : Bool => ()) [(true, z), (false, z')] := by
  rw [hasImageCollision_iff]
  exact ⟨true, by simp, false, by simp, by simp, rfl⟩

/-- The same query cached twice does not trigger `HasImageCollision`. -/
example (z z' : ℕ) : ¬ HasImageCollision (fun _ : Bool => ()) [(true, z), (true, z')] := by
  rw [hasImageCollision_iff]
  rintro ⟨m, hm, m', hm', hne, -⟩
  simp at hm hm'
  exact hne (hm.trans hm'.symm)

/-- For an injective map the error of `closeTo_runWith_memoize_simulate_query` is zero. -/
example {M Y Z α : Type} [DecidableEq M] [DecidableEq Y] {φ : M → Y}
    (hφ : Function.Injective φ) (dist : PMF Z) (program : ProbOracleComp (fun _ : M => Z) α) :
    CloseTo ((ProbOracleComp.runWith (memoize fun _ : M => dist) program []).map Prod.fst)
      ((ProbOracleComp.runWith (answer fun _ : Y => dist)
        (ProbOracleComp.simulate (fun m => ProbOracleComp.query (φ m)) program)
        (fun _ => none)).map Prod.fst) 0 := by
  have h := closeTo_runWith_memoize_simulate_query φ dist program
  have hempty : {x : α × List (M × Z) | HasImageCollision φ x.2} = ∅ :=
    Set.eq_empty_of_forall_notMem fun x => not_hasImageCollision_of_injective hφ x.2
  simpa [hempty] using h

/-- Two distinct queries, returning both answers. -/
private def twoQueries : ProbOracleComp (fun _ : Bool => Bool) (Bool × Bool) :=
  ProbOracleComp.query false >>= fun d₀ =>
    ProbOracleComp.query true >>= fun d₁ => pure (d₀, d₁)

/-- The collision term cannot be dropped. Through the constant map the two answers of
`twoQueries` are equal, while a lazily sampled function on the queries returns `(false, true)`
with positive probability, so the two runs are not `0`-close. -/
example :
    ¬ CloseTo
      ((ProbOracleComp.runWith (memoize fun _ : Bool => PMF.uniformOfFintype Bool) twoQueries
        []).map Prod.fst)
      ((ProbOracleComp.runWith (answer fun _ : Unit => PMF.uniformOfFintype Bool)
        (ProbOracleComp.simulate (fun _ => ProbOracleComp.query ()) twoQueries)
        (fun _ => none)).map Prod.fst) 0 := by
  intro h
  have h1 := h {(false, true)}
  have hthrough : ((ProbOracleComp.runWith (answer fun _ : Unit => PMF.uniformOfFintype Bool)
      (ProbOracleComp.simulate (fun _ => ProbOracleComp.query ()) twoQueries)
      (fun _ => none)).map Prod.fst) (false, true) = 0 := by
    rw [PMF.apply_eq_zero_iff]
    simp only [twoQueries, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query,
      ProbOracleComp.simulate_pure, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure, PMF.support_map, Set.mem_image, PMF.mem_support_bind_iff,
      PMF.support_pure, Set.mem_singleton_iff]
    rintro ⟨x, ⟨y, hy, z, hz, rfl⟩, hx⟩
    rw [answer_of_none _ _ _ rfl] at hy
    simp only [PMF.support_map, Set.mem_image] at hy
    obtain ⟨v, -, rfl⟩ := hy
    rw [answer_of_some _ _ _ v (by simp)] at hz
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp at hx
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton, hthrough, add_zero,
    nonpos_iff_eq_zero, PMF.apply_eq_zero_iff] at h1
  refine h1 ?_
  simp only [twoQueries, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
    ProbOracleComp.runWith_pure, PMF.support_map, Set.mem_image, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff]
  refine ⟨((false, true), [(true, true), (false, false)]),
    ⟨(false, [(false, false)]), ?_, (true, [(true, true), (false, false)]), ?_, rfl⟩, rfl⟩
  · exact (mem_support_memoize_iff _ _ _ _).mpr (Or.inr ⟨rfl, by simp, rfl⟩)
  · exact (mem_support_memoize_iff _ _ _ _).mpr (Or.inr ⟨rfl, by simp, rfl⟩)

end Cslib.RandomOracle
