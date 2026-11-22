/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Languages.Probabilistic.Semantics
public import Mathlib.Data.List.Forall2

/-!
# Traversing a list with an oracle program

Running an oracle program on each entry of a list with ordinary `List.mapM` makes the calls of
the entries one after the other. When each call `q` may be answered by any element of
`possible q`, the possible results of the traversal are exactly the lists whose entries are
possible results of the corresponding programs (`OracleComp.mem_supportWith_mapM_iff`), and the
traversal of `k` entries each costing at most `n` costs at most `k * n`
(`OracleComp.IsCostBounded.mapM`). Folding a list `xs` with `List.foldlM` whose step costs at most
`k` costs at most `xs.length * k` (`OracleComp.IsCostBounded.foldlM`).
This is the oracle analogue of `Cslib.ProbComp.mem_support_mapM_iff`.

## Main results

* `Cslib.OracleComp.mem_supportWith_mapM_iff`: the possible results of a traversal are the
  pointwise possible results.
* `Cslib.OracleComp.IsCostBounded.mapM`: a traversal of a list of length `k` whose entries each
  cost at most `n` costs at most `k * n`.
* `Cslib.OracleComp.QueriesSatisfy.mapM`: a traversal makes only the calls its entries make.
* `Cslib.OracleComp.IsCostBounded.foldlM`: a fold of a list `xs` whose step costs at most `k`
  costs at most `xs.length * k`.
* `Cslib.ProbOracleComp.run_mapM`: running a traversal runs its steps in list order.
* `Cslib.ProbOracleComp.run_mapM_query`: a list of queries to a fixed function returns its image.
-/

public section

namespace Cslib.ProbOracleComp

/-- Running a traversal runs each step with the same oracle. -/
theorem run_mapM {Q I R : Type} {spec : Q → Type} (program : I → ProbOracleComp spec R)
    (xs : List I) (oracle : (q : Q) → ProbComp (spec q)) :
    (xs.mapM program).run oracle = xs.mapM (fun x => (program x).run oracle) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

/-- Against a fixed function, a list of external queries returns the list of its values. -/
theorem run_mapM_query {Q R : Type} (f : Q → R) (xs : List Q) :
    (xs.mapM (query (spec := fun _ : Q => R))).run (fun x => pure (f x)) =
      pure (xs.map f) := by
  simp only [run_mapM, run_query, List.mapM_pure]

end Cslib.ProbOracleComp

namespace Cslib.OracleComp

variable {ι α β : Type} {spec : OracleSpec.{0, 0} ι}

/-- The possible results of a list traversal are the lists whose entries are possible results
of the corresponding programs. -/
theorem mem_supportWith_mapM_iff (possible : (q : ι) → Set (spec q))
    (program : α → OracleComp spec β) (inputs : List α) (outputs : List β) :
    outputs ∈ supportWith possible (inputs.mapM program) ↔
      List.Forall₂ (fun a b => b ∈ supportWith possible (program a)) inputs outputs := by
  induction inputs generalizing outputs with
  | nil =>
    rw [List.mapM_nil, supportWith_pure, Set.mem_singleton_iff, List.forall₂_nil_left_iff]
  | cons a inputs ih =>
    simp only [List.mapM_cons, mem_supportWith_bind_iff, supportWith_pure,
      Set.mem_singleton_iff, ih]
    constructor
    · rintro ⟨b, hb, bs, hbs, rfl⟩
      exact List.Forall₂.cons hb hbs
    · intro h
      cases h with
      | cons hb hbs => exact ⟨_, hb, _, hbs, rfl⟩

/-- A traversal of `inputs` whose entries each cost at most `n` costs at most
`inputs.length * n`. -/
theorem IsCostBounded.mapM {cost : ι → ℕ} {program : α → OracleComp spec β} {n : ℕ}
    {inputs : List α} (h : ∀ a ∈ inputs, IsCostBounded cost (program a) n) :
    IsCostBounded cost (inputs.mapM program) (inputs.length * n) := by
  induction inputs with
  | nil => exact .pure _ _
  | cons a inputs ih =>
    rw [List.mapM_cons, List.length_cons, Nat.add_mul, one_mul, Nat.add_comm]
    exact (h a List.mem_cons_self).bind fun b =>
      ((ih fun a' ha' => h a' (List.mem_cons_of_mem a ha')).bind fun bs => .pure (b :: bs) 0)

/-- A traversal whose entries' calls all satisfy `p` makes only calls satisfying `p`. -/
theorem QueriesSatisfy.mapM {p : ι → Prop} {program : α → OracleComp spec β} {inputs : List α}
    (h : ∀ a ∈ inputs, QueriesSatisfy p (program a)) :
    QueriesSatisfy p (inputs.mapM program) := by
  have h' := IsCostBounded.mapM h
  rw [Nat.mul_zero] at h'
  exact h'

/-- Folding `xs` by steps that each cost at most `k` costs at most `xs.length * k`. -/
theorem IsCostBounded.foldlM.{u, v, w} {ι : Type u} {spec : OracleSpec.{u, v} ι}
    {α : Type v} {β : Type w} {cost : ι → ℕ} {f : α → β → OracleComp spec α} {k : ℕ}
    (hf : ∀ a b, IsCostBounded cost (f a b) k) (init : α) (xs : List β) :
    IsCostBounded cost (xs.foldlM f init) (xs.length * k) := by
  induction xs generalizing init with
  | nil => simp [IsCostBounded.pure]
  | cons x xs ih =>
    rw [List.foldlM_cons, List.length_cons, Nat.add_mul, one_mul, Nat.add_comm]
    exact (hf init x).bind fun a => ih a

end Cslib.OracleComp
