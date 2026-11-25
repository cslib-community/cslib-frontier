/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Control.Monad.Memoize
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Probability.PMF.Bind

/-!
# Query-membership equivalence between lazy memoization and eager random-oracle logs

For an adaptive probabilistic client querying a uniform random function `Q → V` on finite `Q` and
nonempty finite `V`, testing whether a target point `s : Q` appears among the keys of the
association-list cache produced by `memoize` has the same distribution as sampling an eager table
`table ← uniformOfFintype (Q → V)` and testing whether `s` appears in the `runLog` transcript.

## Main results

* `Cslib.RandomOracle.runWith_memoize_mem_eq_eager_runLog`: equality of query-membership indicator
  distributions between lazy list memoization and eager-table `runLog`.
-/

public section

open Cslib Probability
open Cslib.Probability.PMF (uniformOfFintype)

namespace Cslib.RandomOracle

private theorem lookup_isSome_eq_decide_mem_map_fst {Q V : Type} [DecidableEq Q]
    (c : List (Q × V)) (s : Q) :
    (c.lookup s).isSome = decide (s ∈ c.map Prod.fst) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.lookup_isSome_iff, beq_iff_eq, decide_eq_true_eq, List.mem_map]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩⟩

private theorem isSome_of_mem_support_answer {Q V : Type} [DecidableEq Q]
    (d : Q → PMF V) (q s : Q) (c : Cache (fun _ : Q => V))
    {ac : V × Cache (fun _ : Q => V)}
    (hac : ac ∈ (answer d q c).support) :
    (ac.2 s).isSome = ((c s).isSome || decide (q = s)) := by
  cases h : c q with
  | none =>
    simp only [answer_of_none d c q h, PMF.mem_support_map_iff] at hac
    obtain ⟨v, -, rfl⟩ := hac
    by_cases hqs : s = q
    · subst hqs
      simp
    · simp [Function.update_of_ne hqs, Ne.symm hqs]
  | some v =>
    simp only [answer_of_some d c q v h, PMF.mem_support_pure_iff] at hac
    subst hac
    by_cases hqs : s = q
    · subst hqs
      simp [h]
    · simp [Ne.symm hqs]

/-- Testing whether `s : Q` belongs to the cached keys of a lazy `memoize` run from `[]` against
`uniformOfFintype V` has the same distribution as sampling an eager table
`table ← uniformOfFintype (Q → V)` and testing whether `s` belongs to the `runLog` query log. -/
theorem runWith_memoize_mem_eq_eager_runLog {Q V α : Type} [Fintype Q] [DecidableEq Q]
    [Fintype V] [Nonempty V] (M : ProbOracleComp (fun _ : Q => V) α) (s : Q) :
    ((ProbOracleComp.runWith (memoize fun _ : Q => uniformOfFintype V) M []).map
        fun (_, c) => decide (s ∈ c.map Prod.fst)) =
      (uniformOfFintype (Q → V)).bind fun table =>
        (ProbComp.eval (M.runLog fun q => pure (table q))).map
          fun (_, log) => decide (s ∈ log.map Prod.fst) := by
  let d : Q → PMF V := fun _ => uniformOfFintype V
  have hmem : ((ProbOracleComp.runWith (memoize d) M []).map
      fun (_, c) => decide (s ∈ c.map Prod.fst)) =
      (ProbOracleComp.runWith (answer d) M (fun _ => none)).map
        fun (_, c) => (c s).isSome := by
    have h := congrArg (PMF.map fun (p : α × Cache (fun _ : Q => V)) => (p.2 s).isSome)
      (run_interpret_memoize_prob d M [])
    simpa only [PMF.map_comp, Function.comp_def, ofList_nil, ofList,
      lookup_isSome_eq_decide_mem_map_fst] using h
  rw [hmem]
  let hitOracle : Q → StateT ((Q → V) × Bool) PMF V :=
    fun q ⟨table, hit⟩ => PMF.pure (table q, (table, hit || decide (q = s)))
  let relate : Cache (fun _ : Q => V) → PMF ((Q → V) × Bool) :=
    fun c => (complete d c).map fun table => (table, (c s).isSome)
  have hsim := ProbOracleComp.runWith_simulation (answer d) hitOracle relate
    (fun q c => by
      have hcongr : ((answer d q c).bind fun ⟨a, c'⟩ =>
          (relate c').map (a, ·)) =
          ((answer d q c).bind fun ⟨a, c'⟩ =>
            (complete d c').map (a, ·)).map
              fun ⟨a, table⟩ => (a, (table, (c s).isSome || decide (q = s))) := by
        rw [PMF.map_bind]
        refine PMF.bind_congr_on_support _ _ _ fun ac hac => ?_
        simp only [relate, PMF.map_comp, Function.comp_def,
          isSome_of_mem_support_answer d q s c hac]
      rw [hcongr]
      have hcomp := congrArg
        (PMF.map fun ⟨a, table⟩ => (a, (table, (c s).isSome || decide (q = s))))
        (answer_complete d c q)
      simpa only [relate, hitOracle, PMF.monad_bind_eq_bind, PMF.map_comp, PMF.bind_map,
        Function.comp_def, PMF.pure_bind, PMF.map, PMF.bind_bind] using hcomp)
    M (fun _ => none)
  have hproj := congrArg (PMF.map fun (_, _, hit) => hit) hsim
  have hlhs : (((ProbOracleComp.runWith (answer d) M (fun _ => none)).bind
      fun ⟨a, c'⟩ => (relate c').map (a, ·)).map fun (_, _, hit) => hit) =
      (ProbOracleComp.runWith (answer d) M (fun _ => none)).map
        fun (_, c') => (c' s).isSome := by
    rw [PMF.map_bind]
    have hconst (ac : α × Cache (fun _ : Q => V)) :
        ((relate ac.2).map (ac.1, ·)).map (fun (_, _, hit) => hit) =
          PMF.pure (ac.2 s).isSome := by
      simp only [relate, PMF.map_comp, Function.comp_def]
      exact (complete d ac.2).map_const (ac.2 s).isSome
    simp only [hconst]
    rfl
  rw [← hlhs, hproj]
  simp only [relate, complete_empty, d, PMF.pi_uniformOfFintype, PMF.bind_map,
    PMF.map_bind, Function.comp_def, Option.isSome_none]
  refine congrArg ((uniformOfFintype (Q → V)).bind ·) (funext fun table => ?_)
  have hlog : ProbComp.eval (M.runLog fun q => pure (table q)) =
      ProbOracleComp.runWith (fun q log => PMF.pure (table q, log ++ [(q, table q)])) M [] := by
    rw [ProbOracleComp.runLog, ProbOracleComp.eval_runState]
    simp only [ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map]
  rw [hlog]
  have hstate := ProbOracleComp.runWith_map_state
    (fun q (log : List (Q × V)) => PMF.pure (table q, log ++ [(q, table q)]))
    hitOracle (fun log => (table, decide (s ∈ log.map Prod.fst)))
    (fun q log => by
      simp only [hitOracle, PMF.pure_map, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton]
      congr 2
      cases hs : decide (s ∈ List.map Prod.fst log) <;>
        cases hq : decide (q = s) <;> simp_all [eq_comm])
    M []
  have hstate' := congrArg (PMF.map fun (_, _, hit) => hit) hstate
  simpa only [PMF.map_comp, Function.comp_def, List.map_nil, List.not_mem_nil, decide_false] using
    hstate'.symm

end Cslib.RandomOracle
