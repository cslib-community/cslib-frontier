/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Domain
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount

/-!
# Adaptive routing for cascade child queries

At a cut between blocks, the router assigns a channel to a parent prefix when a long query
first visits it. Later queries to the same parent use that channel. The next block is the child
query, and the cascade processes the remaining suffix from the returned label. Short queries
use a local label cache.

This is the query routing step for the adjacent hybrids of [BonehShoup2023], v0.6, Sections 4.6.1
(printed pp. 152–154) and 6.4.2 (printed pp. 229–230). It supplies the external query-count
bound. The distribution law and polynomial-time certificate are separate from this bound.

## Main definitions

* `Cslib.Crypto.cascadeChildRouter`: the adaptive client of the child oracle.

## Main results

* `Cslib.Crypto.isQueryBounded_cascadeChildRouter`: the router preserves the client's
  external query budget.
-/

public section

namespace Cslib.Crypto

open Probability

/-- State of the adaptive router. A parent's position in `parents` is its channel number. -/
structure CascadeChildRouterState where
  /-- Parent prefixes of previously forwarded queries, in order of first appearance. -/
  parents : List (List Bool)
  /-- Uniform labels already assigned to valid queries ending at or before the cut. -/
  shortLabels : List (List Bool × List Bool)

/-- Route one cascade query. An invalid query leaves the state untouched.
A long query sends its next block to the channel for its parent prefix. Only the first
`n` bits of a child reply are used, which preserves replies of the intended width. -/
@[expose]
noncomputable def cascadeChildRoute (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ) (query : List Bool)
    (state : CascadeChildRouterState) : WordOracleComp ℕ (List Bool × CascadeChildRouterState) :=
  if valid query then
    let width := inLen n
    let cut := depth * width
    if cut < query.length then do
      let parent := query.take cut
      let channel := state.parents.idxOf parent
      let parents := if channel = state.parents.length then state.parents ++ [parent]
        else state.parents
      let suffix := query.drop cut
      let label ← ProbOracleComp.query (spec := fun _ : ℕ × List Bool => List Bool)
        (channel, suffix.take width)
      return (cascadeFamily inLen family (label.take n) (suffix.drop width),
        { state with parents })
    else do
      let (label, shortLabels) ← ProbOracleComp.sample
        (cachedRandomFunctionOracle (fun _ => true) n query state.shortLabels)
      return (label, { state with shortLabels })
  else pure ([], state)

/-- Run the adaptive client using private random labels and child-oracle channels numbered
by the order in which parent prefixes are first encountered. -/
@[expose]
noncomputable def cascadeChildRouter (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ)
    (program : WordOracleComp Unit Bool) : WordOracleComp ℕ Bool :=
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (fun request state => cascadeChildRoute valid inLen family n depth request.2 state))
    program).run ⟨[], []⟩

/-- Each original external query produces at most one child-oracle query. -/
theorem isQueryBounded_cascadeChildRouter (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ)
    {program : WordOracleComp Unit Bool} {budget : ℕ}
    (h : program.IsQueryBounded budget) :
    (cascadeChildRouter valid inLen family n depth program).IsQueryBounded budget := by
  refine (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (OracleComp.IsCostBounded.run_interpret (fun q state => ?_) h _)
  cases q with
  | inl k =>
    rw [OracleComp.sumHandler, StateT.run_lift, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.sample _)
  | inr q =>
    dsimp only [OracleComp.sumHandler, cascadeChildRoute]
    split
    · split
      · exact (ProbOracleComp.IsQueryBounded.query _).bind fun _ => .pure _ 0
      · exact ((ProbOracleComp.IsQueryBounded.sample _).bind fun _ => .pure _ 0).mono
          (Nat.zero_le 1)
    · exact .pure _ _

end Cslib.Crypto
