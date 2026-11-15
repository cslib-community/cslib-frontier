/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test suite)

import CslibFrontier.Languages.Probabilistic.RandomOracle.Through

/-!
# Tests for `CslibFrontier.Languages.Probabilistic.RandomOracle.Through`

Checks `HasImageCollision` and `closeTo_runWith_memoize_memoizeThrough` as module-form clients on
injective and colliding maps and duplicate cached queries.
-/

set_option linter.privateModule false

namespace Cslib.RandomOracle

open Probability

/-- An injective map has no image collision on any cache. -/
example {M Y Z : Type} {φ : M → Y} (hφ : Function.Injective φ) (cache : List (M × Z)) :
    ¬ HasImageCollision φ cache := by
  rw [hasImageCollision_iff]
  rintro ⟨m, -, m', -, hne, h⟩
  exact hne (hφ h)

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

private theorem hasImageCollision_set_eq_empty {M Y Z : Type} {φ : M → Y}
    (hφ : Function.Injective φ) :
    ∀ α : Type, {x : α × List (M × Z) | HasImageCollision φ x.2} = ∅ := by
  intro α
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rw [hasImageCollision_iff]
  rintro ⟨m, -, m', -, hne, h⟩
  exact hne (hφ h)

/-- For an injective map `φ`, the error of `closeTo_runWith_memoize_memoizeThrough` is zero. -/
example {M Y Z α : Type} [DecidableEq M] [DecidableEq Y] {φ : M → Y}
    (hφ : Function.Injective φ) (dist : PMF Z) (program : ProbOracleComp (fun _ : M => Z) α) :
    CloseTo ((ProbOracleComp.runWith (memoize fun _ : M => dist) program []).map Prod.fst)
      ((ProbOracleComp.runWith (memoizeThrough φ dist) program []).map Prod.fst) 0 := by
  have h := closeTo_runWith_memoize_memoizeThrough φ dist program
  simpa [hasImageCollision_set_eq_empty hφ α] using h

/-- Combining `closeTo_runWith_memoize_memoizeThrough` with `runWith_memoizeThrough_map_fst`
replaces a lazy random oracle on `M` by `φ`-substituted calls to a lazy random oracle on `Y`
with zero error when `φ` is injective. -/
example {M Y Z α : Type} [DecidableEq M] [DecidableEq Y] {φ : M → Y}
    (hφ : Function.Injective φ) (dist : PMF Z) (program : ProbOracleComp (fun _ : M => Z) α) :
    CloseTo ((ProbOracleComp.runWith (memoize fun _ : M => dist) program []).map Prod.fst)
      ((ProbOracleComp.runWith (answer fun _ : Y => dist)
        (ProbOracleComp.simulate (fun m => ProbOracleComp.query (φ m)) program)
        (fun _ => none)).map Prod.fst) 0 := by
  rw [← runWith_memoizeThrough_map_fst]
  have h := closeTo_runWith_memoize_memoizeThrough φ dist program
  simpa [hasImageCollision_set_eq_empty hφ α] using h

end Cslib.RandomOracle
