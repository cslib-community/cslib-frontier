/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.QueriesWith
public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.Sum

/-!
# Cost and request decompositions for deterministic runs

Connects the request trace `OracleComp.queriesWith` of a deterministic run to `IsCostBounded`,
summed interfaces `liftLeft`, and short-circuiting list searches `List.findSomeM?`.

## Main results

* `Cslib.OracleComp.IsCostBounded.sum_map_queriesWith_le`: weighted cost along a run stays within
  a pathwise `IsCostBounded` budget.
* `Cslib.OracleComp.queriesWith_liftLeft`: requests of an embedded left program under `sumPure` are
  its left requests mapped by `Sum.inl`.
* `Cslib.OracleComp.queriesWith_findSomeM?_cons`: requests of a `findSomeM?` step, continuing into
  the tail only when the step returns `none`.
* `Cslib.OracleComp.queriesWith_findSomeM?_of_forall_eq_none`: requests of a `findSomeM?` search
  where every step evaluates to `none` concatenate the requests of all steps.
-/

public section

namespace Cslib.OracleComp

section Cost

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- A program that stays within `n` for `cost` on every path spends at most `n` along the run
against `answer`. The weighted form of `IsQueryBounded.length_queriesWith_le`. -/
theorem IsCostBounded.sum_map_queriesWith_le {cost : ι → ℕ} (answer : (q : ι) → spec q)
    {program : OracleComp spec α} {n : ℕ} (h : IsCostBounded cost program n) :
    ((queriesWith answer program).map cost).sum ≤ n := by
  induction h with
  | pure a n => simp only [queriesWith_pure, List.map_nil, List.sum_nil, Nat.zero_le]
  | liftBind q cont n _ ih =>
    rw [queriesWith_query_bind, List.map_cons, List.sum_cons, Nat.add_comm]
    exact Nat.add_le_add_right (ih (answer q)) (cost q)

end Cost

section Lift

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {α : Type}

/-- The requests of an embedded left program are its own requests, on the left. -/
theorem queriesWith_liftLeft (o₁ : (q : ι₁) → spec₁ q) (o₂ : (q : ι₂) → spec₂ q)
    (prog : OracleComp spec₁ α) :
    queriesWith (sumPure o₁ o₂) (liftLeft (spec₂ := spec₂) prog) =
      (queriesWith o₁ prog).map Sum.inl := by
  induction prog using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [liftLeft_freeMBind, liftLeft_query]
    exact congrArg (Sum.inl q :: ·) (ih (o₁ q))

end Lift

section FindSomeM

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- The requests of a search: those of its first step, then those of the rest when that step
finds nothing. -/
theorem queriesWith_findSomeM?_cons (o : (q : ι) → spec q)
    (f : α → OracleComp spec (Option β)) (x : α) (xs : List α) :
    queriesWith o ((x :: xs).findSomeM? f) =
      queriesWith o (f x) ++
        if (evalPure o (f x)).isSome then [] else queriesWith o (xs.findSomeM? f) := by
  rw [List.findSomeM?_cons, queriesWith_bind]
  refine congrArg (queriesWith o (f x) ++ ·) ?_
  have hsub : ∀ (y₁ y₂ : Option β), y₁ = y₂ →
      queriesWith o (match y₁ with | some b => pure (some b) | none => xs.findSomeM? f) =
        if y₂.isSome then [] else queriesWith o (xs.findSomeM? f) := by
    rintro y₁ y₂ rfl
    grind [queriesWith_pure]
  exact hsub _ _ rfl

/-- A search in which no step finds anything makes the requests of all its steps, in order. -/
theorem queriesWith_findSomeM?_of_forall_eq_none (o : (q : ι) → spec q)
    (f : α → OracleComp spec (Option β)) {xs : List α}
    (h : ∀ x ∈ xs, evalPure o (f x) = none) :
    queriesWith o (xs.findSomeM? f) = xs.flatMap fun x => queriesWith o (f x) := by
  induction xs with
  | nil => rw [List.findSomeM?_nil, queriesWith_pure, List.flatMap_nil]
  | cons x xs ih =>
    rw [queriesWith_findSomeM?_cons, h x List.mem_cons_self]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      ih fun x' hx' => h x' (List.mem_cons_of_mem x hx'), List.flatMap_cons]

end FindSomeM

end Cslib.OracleComp
