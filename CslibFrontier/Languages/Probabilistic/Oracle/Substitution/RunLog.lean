/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution

/-!
# Logged runs of oracle queries and query-renaming substitutions

`ProbOracleComp.runLog` executes a randomized oracle program against a memoryless oracle while
appending each `(query, reply)` pair to the transcript. This module provides the basic equations
for `pure`, `query`, `map`, single-query programs `do let reply ← query q; return f reply`
(together with their `IsQueryBounded 1` witness), and query-renaming substitutions
`ProbOracleComp.simulate (fun q => ProbOracleComp.query (encode q))`.

## Main results

* `Cslib.ProbOracleComp.runLog_pure`, `Cslib.ProbOracleComp.runLog_query`,
  `Cslib.ProbOracleComp.runLog_map`: `runLog` equations for `pure`, `query`, and `map`.
* `Cslib.ProbOracleComp.runLog_query_bind_pure`,
  `Cslib.ProbOracleComp.IsQueryBounded.query_bind_pure`: logged execution and one-query bound for
  a single query followed by deterministic postprocessing.
* `Cslib.ProbOracleComp.runLog_simulate_query`: substituting `q ↦ query (encode q)` runs the
  original program against `oracle ∘ encode` and maps the logged requests by `encode`.
-/

public section

namespace Cslib.ProbOracleComp

variable {Q T R α β : Type}

/-- Returning a value makes no oracle call and leaves the log empty. -/
@[simp] theorem runLog_pure (a : α) (oracle : Q → ProbComp R) :
    (pure a : ProbOracleComp (fun _ : Q => R) α).runLog oracle = pure (a, []) :=
  rfl

/-- A single external query runs `oracle q` once and records `(q, reply)`. -/
@[simp] theorem runLog_query (q : Q) (oracle : Q → ProbComp R) :
    (query q : ProbOracleComp (fun _ : Q => R) R).runLog oracle =
      (fun reply => (reply, [(q, reply)])) <$> oracle q := by
  simp [runLog, StateT.run]

/-- Deterministic postprocessing transforms the returned value and keeps the logged transcript. -/
theorem runLog_map (f : α → β) (A : ProbOracleComp (fun _ : Q => R) α)
    (oracle : Q → ProbComp R) :
    (f <$> A).runLog oracle = Prod.map f id <$> A.runLog oracle := by
  simp only [runLog, runState_map, StateT.run_map]
  rfl

/-- One external query followed by a pure return logs `(q, reply)` and transforms the reply. -/
theorem runLog_query_bind_pure (q : Q) (f : R → α) (oracle : Q → ProbComp R) :
    (query q >>= fun reply => (pure (f reply) : ProbOracleComp (fun _ : Q => R) α)).runLog oracle =
      (fun reply => (f reply, [(q, reply)])) <$> oracle q := by
  simp only [bind_pure_comp, runLog_map, runLog_query, Functor.map_map]
  rfl

/-- One external query followed by a pure return makes at most one oracle call on every path. -/
theorem IsQueryBounded.query_bind_pure (q : Q) (f : R → α) :
    (ProbOracleComp.query (spec := fun _ : Q => R) q >>= fun reply =>
      pure (f reply)).IsQueryBounded 1 := by
  simpa only [bind_pure_comp, IsQueryBounded, OracleComp.isCostBounded_map_iff] using
    IsQueryBounded.query q

private theorem runState_simulate_query (encode : Q → T)
    (A : ProbOracleComp (fun _ : Q => R) α) (oracle : T → ProbComp R)
    (log : List (Q × R)) :
    ((simulate (fun q => query (encode q)) A).runState
      (fun q seen => (fun reply => (reply, seen ++ [(q, reply)])) <$> oracle q)).run
        (log.map fun entry => (encode entry.1, entry.2)) =
      (fun result => (result.1, result.2.map fun entry => (encode entry.1, entry.2))) <$>
        (A.runState (fun q seen =>
          (fun reply => (reply, seen ++ [(q, reply)])) <$> oracle (encode q))).run log := by
  induction A using ProbOracleComp.induction generalizing log with
  | pure a => simp
  | sample_bind n cont ih =>
    simp only [simulate_bind, simulate_sample, runState_bind, runState_sample,
      StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
    exact bind_congr fun value => ih value log
  | query_bind q cont ih =>
    simp only [simulate_bind, simulate_query, runState_bind, runState_query, StateT.run_bind]
    simp only [StateT.run, bind_map_left, map_bind]
    apply bind_congr
    intro reply
    simpa only [StateT.run, List.map_append, List.map_cons, List.map_nil] using
      ih reply (log ++ [(q, reply)])

/-- Substituting each query `q` with `query (encode q)` runs `A` against `oracle ∘ encode` and
renames every logged request by `encode`. -/
theorem runLog_simulate_query (encode : Q → T)
    (A : ProbOracleComp (fun _ : Q => R) α) (oracle : T → ProbComp R) :
    (simulate (fun q => query (encode q)) A).runLog oracle =
      (fun result => (result.1, result.2.map fun entry => (encode entry.1, entry.2))) <$>
        A.runLog (fun q => oracle (encode q)) :=
  runState_simulate_query encode A oracle []

end Cslib.ProbOracleComp
