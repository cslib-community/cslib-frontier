/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.Control.Monad.FindM
import CslibFrontier.Languages.Probabilistic.Traverse.FindM

/-! Clients of `List.findM?_cons`, `OracleComp.evalPure_findM?`,
`OracleComp.IsCostBounded.findM?`, and `OracleComp.QueriesSatisfy.findM?` under module
encapsulation. -/

namespace CslibFrontierTests.OracleFindM

open Cslib

/-- A search against a concrete oracle: the first `x` whose square is `9`. -/
example : OracleComp.evalPure (spec := fun _ : ℕ => ℕ) (fun n => n * n)
    ([1, 2, 3, 4].findM? fun x =>
      (fun y => decide (y = 9)) <$> OracleComp.query (spec := fun _ : ℕ => ℕ) x) = some 3 := by
  rw [OracleComp.evalPure_findM?]
  simp [OracleComp.evalPure_map, OracleComp.evalPure_query]

/-- No element passes: the search returns `none`. -/
example : OracleComp.evalPure (spec := fun _ : ℕ => ℕ) (fun n => n * n)
    ([1, 2, 4].findM? fun x =>
      (fun y => decide (y = 9)) <$> OracleComp.query (spec := fun _ : ℕ => ℕ) x) = none := by
  rw [OracleComp.evalPure_findM?]
  simp [OracleComp.evalPure_map, OracleComp.evalPure_query]

/-- A test that makes two calls: the search costs at most `xs.length * 2`. -/
example (xs : List ℕ) :
    OracleComp.IsQueryBounded (spec := fun _ : ℕ => ℕ)
      (xs.findM? fun x => do
        let a ← OracleComp.query (spec := fun _ : ℕ => ℕ) x
        let b ← OracleComp.query (spec := fun _ : ℕ => ℕ) a
        return decide (b = 0)) (xs.length * 2) :=
  OracleComp.IsCostBounded.findM? fun x _ =>
    OracleComp.IsCostBounded.bind (cost := fun _ : ℕ => 1) (n := 1) (m := 1)
      (OracleComp.IsCostBounded.query x) fun a =>
        OracleComp.IsCostBounded.bind (cost := fun _ : ℕ => 1) (n := 1) (m := 0)
          (OracleComp.IsCostBounded.query a) fun _ => .pure _ 0

/-- A weighted cost: calls at even points are free, so a search over even points costs nothing. -/
example (xs : List ℕ) (h : ∀ x ∈ xs, x % 2 = 0) :
    OracleComp.IsCostBounded (spec := fun _ : ℕ => Bool) (fun q => q % 2)
      (xs.findM? fun x => OracleComp.query (spec := fun _ : ℕ => Bool) x) (xs.length * 0) :=
  OracleComp.IsCostBounded.findM? fun x hx => by
    have := OracleComp.IsCostBounded.query (spec := fun _ : ℕ => Bool) (cost := fun q => q % 2) x
    simpa [h x hx] using this

/-- The search calls the oracle only where its tests do. -/
example (xs : List ℕ) :
    OracleComp.QueriesSatisfy (spec := fun _ : ℕ => Bool) (fun q => q ∈ xs)
      (xs.findM? fun x => OracleComp.query (spec := fun _ : ℕ => Bool) x) :=
  OracleComp.QueriesSatisfy.findM? fun _ hx => OracleComp.QueriesSatisfy.query hx

/-- The unfolding step in any monad. -/
example (p : ℕ → Option Bool) (a : ℕ) (as : List ℕ) :
    (a :: as).findM? p = p a >>= fun b => if b then pure (some a) else as.findM? p :=
  List.findM?_cons p a as

end CslibFrontierTests.OracleFindM
