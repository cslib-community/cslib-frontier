/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Languages.Probabilistic.RandomOracle.ImageCollision
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Foundations.Data.List.SortedAssoc
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag

/-!
# Lazily sampled function called through a map

A program queries `m : M`, and each query is answered by a lazily sampled function on `Y` at
`φ m`. Its result is statistically close to its result against a lazily sampled function on `M`
itself; the error is the probability that the queries of the second run contain two distinct
`m`, `m'` with `φ m = φ m'`.

## Main results

* `Cslib.RandomOracle.closeTo_runWith_memoize_simulate_query`: the closeness statement above.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Version 0.6,
  Section 7.3, proof of Theorem 7.7, Games 1 and 2 (p. 264), an application of the Difference
  Lemma (Theorem 4.7).
-/

public section

namespace Cslib.RandomOracle

open Probability OracleComp

variable {M Y Z α : Type} [BEq M] [LawfulBEq M] [DecidableEq Y]

/-- Lazy sampling of a function on `Y` that is called at `φ m`, with the cache kept by query. In
the cache-hit branch, `(m, z)` is still recorded when `m` is not yet cached so that `cache`
retains every distinct query after an image collision. -/
private noncomputable def memoizeThrough (φ : M → Y) (dist : PMF Z) (m : M) :
    StateT (List (M × Z)) PMF Z := fun cache =>
  match (cache.map (Prod.map φ id)).lookup (φ m) with
  | some z => PMF.pure (z, if (cache.lookup m).isSome then cache else (m, z) :: cache)
  | none => dist.map fun z => (z, (m, z) :: cache)

private theorem lookup_map_of_lookup (φ : M → Y) {cache : List (M × Z)} {m : M} {z : Z}
    (hgood : ¬HasImageCollision φ cache) (h : cache.lookup m = some z) :
    (cache.map (Prod.map φ id)).lookup (φ m) = some z := by
  induction cache with
  | nil => simp at h
  | cons e t ih =>
    rcases e with ⟨m₀, z₀⟩
    by_cases hm : m = m₀
    · subst hm
      simpa using h
    · simp only [List.lookup_cons, show (m == m₀) = false by simpa using hm] at h
      have hφ : φ m ≠ φ m₀ := fun heq =>
        hgood ⟨(m, z), List.mem_cons_of_mem _ (List.mem_of_lookup_eq_some h),
          (m₀, z₀), List.mem_cons_self, hm, heq⟩
      simpa only [List.map_cons, Prod.map_apply, id_eq, List.lookup_cons,
        show (φ m == φ m₀) = false by simpa using hφ] using
        ih (fun hbad => hgood (hbad.mono (List.subset_cons_self _ _))) h

private theorem hasImageCollision_cons_of_lookup (φ : M → Y) {cache : List (M × Z)} {m : M} {z : Z}
    (hm : cache.lookup m = none)
    (hy : (cache.map (Prod.map φ id)).lookup (φ m) = some z) (z' : Z) :
    HasImageCollision φ ((m, z') :: cache) := by
  obtain ⟨e, he, heq⟩ := List.mem_map.1 (List.mem_of_lookup_eq_some hy)
  refine ⟨(m, z'), by simp, e, List.mem_cons_of_mem _ he, fun hm_eq => ?_,
    (congrArg Prod.fst heq).symm⟩
  exact bne_iff_ne.mp (List.lookup_eq_none_iff.mp hm e he) hm_eq

omit [LawfulBEq M] in
private theorem memoizeThrough_map_ofList (φ : M → Y) (dist : PMF Z) (m : M)
    (cache : List (M × Z)) :
    (memoizeThrough φ dist m cache).map
        (fun x => (x.1, ofList (x.2.map (Prod.map φ id)))) =
      answer (fun _ : Y => dist) (φ m) (ofList (cache.map (Prod.map φ id))) := by
  unfold memoizeThrough
  cases hy : (cache.map (Prod.map φ id)).lookup (φ m) with
  | none =>
    rw [answer_of_none (fun _ : Y => dist) _ (φ m) hy, PMF.map_comp]
    exact congrArg (PMF.map · dist) (funext fun z => by
      simp only [Function.comp_apply, List.map_cons, Prod.map_apply, id_eq, ofList_cons])
  | some z =>
    rw [answer_of_some (fun _ : Y => dist) _ (φ m) z hy, PMF.pure_map]
    refine congrArg PMF.pure (Prod.ext rfl ?_)
    by_cases hm : (cache.lookup m).isSome
    · simp only [hm, ite_true]
    · simp only [hm, Bool.false_eq_true, ite_false, List.map_cons, Prod.map_apply, id_eq,
        ofList_cons]
      exact Function.update_eq_self_iff.mpr
        (show some z = ofList (cache.map (Prod.map φ id)) (φ m) from hy.symm)

/-- The lazy function called through `φ` and the lazy function on the queries agree until two
distinct queries have the same image. -/
private theorem identicalUntilBad_memoizeThrough (φ : M → Y) (dist : PMF Z) :
    OracleComp.IdenticalUntilBad (memoizeThrough φ dist)
      (memoize (fun _ : M => dist)) (HasImageCollision φ) where
  agree m s hs a s' hs' := by
    cases hm : s.lookup m with
    | some z =>
      have hy := lookup_map_of_lookup φ hs hm
      rw [memoize_of_some _ _ _ z hm]
      simp only [memoizeThrough, hy, hm, Option.isSome_some, ite_true]
      rfl
    | none =>
      cases hy : (s.map (Prod.map φ id)).lookup (φ m) with
      | none =>
        simp only [memoizeThrough, hy, memoize, hm]
        rfl
      | some z =>
        have hbad := hasImageCollision_cons_of_lookup φ hm hy
        have h1 : memoizeThrough φ dist m s (a, s') = 0 := by
          simp only [memoizeThrough, hy, hm, Option.isSome_none, Bool.false_eq_true, ite_false]
          rw [PMF.apply_eq_zero_iff, PMF.support_pure, Set.mem_singleton_iff]
          intro h
          have h' : s' = (m, z) :: s := (Prod.mk.inj h).2
          exact hs' (h' ▸ hbad z)
        have h2 : memoize (fun _ : M => dist) m s (a, s') = 0 := by
          rw [PMF.apply_eq_zero_iff]
          intro hmem
          rcases (mem_support_memoize_iff _ _ _ _).mp hmem with ⟨h, -⟩ | ⟨-, -, h⟩
          · rw [hm] at h; exact absurd h (by simp)
          · have h' : s' = (m, a) :: s := h
            exact hs' (h' ▸ hbad a)
        rw [h1, h2]
  absorb_first m s hs x hx := by
    refine hs.mono fun p hp => ?_
    simp only [memoizeThrough] at hx
    split at hx
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      dsimp only
      split
      · exact hp
      · exact List.mem_cons_of_mem _ hp
    · simp only [PMF.support_map, Set.mem_image] at hx
      obtain ⟨z, -, rfl⟩ := hx
      exact List.mem_cons_of_mem _ hp
  absorb_second m s hs x hx := by
    refine hs.mono fun p hp => ?_
    rcases (mem_support_memoize_iff _ _ _ _).mp hx with ⟨-, h⟩ | ⟨-, -, h⟩
    · exact h ▸ hp
    · exact h ▸ List.mem_cons_of_mem _ hp

omit [LawfulBEq M] in
/-- The result of a program run against `memoizeThrough φ dist` is its result when each query `m`
is replaced by the query `φ m` to a lazily sampled function on `Y`. -/
private theorem runWith_memoizeThrough_map_fst (φ : M → Y) (dist : PMF Z)
    (program : ProbOracleComp (fun _ : M => Z) α) :
    (ProbOracleComp.runWith (memoizeThrough φ dist) program []).map Prod.fst =
      (ProbOracleComp.runWith (answer fun _ : Y => dist)
        (ProbOracleComp.simulate (fun m => ProbOracleComp.query (φ m)) program)
        (fun _ => none)).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) <|
    ProbOracleComp.runWith_map_state (memoizeThrough φ dist)
      (fun m => answer (fun _ : Y => dist) (φ m))
      (fun cache => ofList (cache.map (Prod.map φ id)))
      (fun m cache => memoizeThrough_map_ofList φ dist m cache) program []
  simpa only [runWith_norm, pmf_norm, List.map_nil, ofList_nil] using h

/-- **A lazily sampled function called through `φ`.** Replacing each query `m` of `program` by the
query `φ m` to a lazily sampled function on `Y` changes the law of the result by at most the
probability that, in the run against a lazily sampled function on the queries themselves, the
final cache holds two distinct queries with the same image. -/
theorem closeTo_runWith_memoize_simulate_query (φ : M → Y) (dist : PMF Z)
    (program : ProbOracleComp (fun _ : M => Z) α) :
    CloseTo ((ProbOracleComp.runWith (memoize fun _ : M => dist) program []).map Prod.fst)
      ((ProbOracleComp.runWith (answer fun _ : Y => dist)
        (ProbOracleComp.simulate (fun m => ProbOracleComp.query (φ m)) program)
        (fun _ => none)).map Prod.fst)
      ((ProbOracleComp.runWith (memoize fun _ : M => dist) program []).toOuterMeasure
        {x | HasImageCollision φ x.2}) := by
  rw [← runWith_memoizeThrough_map_fst]
  exact ((identicalUntilBad_memoizeThrough φ dist).symm.probOracleComp.closeTo_run program []).map
    Prod.fst

end Cslib.RandomOracle
