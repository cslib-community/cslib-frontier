/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.SelectDistinct
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared

/-!
# Constraint satisfaction problems

A constraint satisfaction problem (CSP) instance `F : CSP Rel V` over a relation alphabet `Rel`
and variable type `V` is a conjunction (list) of constraints `⟨R, vs⟩ : Constraint Rel V`,
interpreted over a domain `D` under a family of relations `sem : Rel → List D → Bool` by requiring
`sem R (vs.map σ) = true` for every `⟨R, vs⟩ ∈ F`.

Relations are not assigned fixed arities at the type level: `sem R` is evaluated at the length of
each constraint's scope `c.scope`. Under a uniform scope-length bound `c.scope.length ≤ k`, each
relation symbol induces a relation of arity at most `k`.

For any finite inhabited domain `D`, `CSP.modelCountOn sem F declared` counts assignments on a
declared finite set of variables `declared : Finset V` (extended by `default` outside `declared`)
that satisfy `F`, and `CSP.modelCount sem F` counts satisfying assignments on the occurring
variables `F.vars.toFinset`. In the Boolean case `D = Bool`, `default = false`, matching
`CNF.modelCountOn` and `CNF.modelCount`.

## Main definitions

* `Cslib.Logic.PL.Constraint`, `Cslib.Logic.PL.CSP`: constraints, with fields `rel` and `scope`,
  and CSP instances. `Cslib.Logic.PL.Constraint.equivProd` identifies a constraint with the pair
  of its fields.
* `Cslib.Logic.PL.Constraint.eval`, `Cslib.Logic.PL.CSP.eval`, `Cslib.Logic.PL.CSP.Satisfiable`:
  evaluation and satisfiability over an arbitrary domain `D`.
* `Cslib.Logic.PL.CSP.vars`, `Cslib.Logic.PL.CSP.numVars`, `Cslib.Logic.PL.CSP.distinctVars`:
  variable occurrences, count of distinct variables, and first-occurrence variable list.
* `Cslib.Logic.PL.Constraint.relabel`, `Cslib.Logic.PL.CSP.relabel`,
  `Cslib.Logic.PL.CSP.denseRelabel`: variable renaming and dense `0, …, numVars - 1` relabeling.
* `Cslib.Logic.PL.CSP.modelCountOn`, `Cslib.Logic.PL.CSP.modelCount`: declared-variable and
  occurring-variable model counts over a finite inhabited domain `D`.
* `Cslib.Logic.PL.CSP.validDeclaredCSP`: executable guard checking scope lengths `≤ k` and
  variable indices `< N`.
* `Cslib.Logic.PL.CSP.KCSP`: the bounded-arity CSP decision problem.

## Main results

* `Cslib.Logic.PL.CSP.vars_denseRelabel_toFinset`, `Cslib.Logic.PL.CSP.numVars_denseRelabel`:
  dense relabeling maps occurring variables onto `Finset.range F.numVars`.
* `Cslib.Logic.PL.CSP.modelCountOn_denseRelabel`, `Cslib.Logic.PL.CSP.modelCount_denseRelabel`:
  dense relabeling preserves declared and occurring model counts.
* `Cslib.Logic.PL.CSP.modelCount_pos_iff`: a CSP instance is satisfiable iff its model count is
  positive.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- A constraint over relation alphabet `Rel` and variable type `V`: a relation symbol `rel` applied
to an ordered `scope` of variables. Relations are not assigned fixed arities at the type level; a
semantics `sem : Rel → List D → Bool` is read at the length of each scope. -/
@[ext]
structure Constraint (Rel V : Type*) where
  /-- The relation symbol applied to the scope. -/
  rel : Rel
  /-- The variables the relation is applied to, in order. -/
  scope : List V
  deriving DecidableEq, Repr

/-- A constraint satisfaction problem (CSP) instance over relation alphabet `Rel` and variable type
`V` is a conjunction (list) of constraints. -/
abbrev CSP (Rel V : Type*) : Type _ := List (Constraint Rel V)

namespace Constraint

variable {Rel V W D : Type*}

/-- A constraint is its relation symbol together with its scope. -/
def equivProd : Constraint Rel V ≃ Rel × List V where
  toFun c := (c.rel, c.scope)
  invFun p := ⟨p.1, p.2⟩

/-- Evaluate a constraint `⟨R, vs⟩` under assignment `σ : V → D` and semantics
`sem : Rel → List D → Bool`. -/
def eval (sem : Rel → List D → Bool) (σ : V → D) (c : Constraint Rel V) : Bool :=
  sem c.rel (c.scope.map σ)

/-- Rename variables in a constraint's scope. -/
def relabel (f : V → W) (c : Constraint Rel V) : Constraint Rel W :=
  ⟨c.rel, c.scope.map f⟩

/-- Evaluating a relabeled constraint composes the assignment with the relabeling. -/
@[simp]
theorem eval_relabel (sem : Rel → List D → Bool) (f : V → W) (σ : W → D)
    (c : Constraint Rel V) :
    eval sem σ (relabel f c) = eval sem (σ ∘ f) c := by
  simp [eval, relabel, List.map_map]

/-- Constraint evaluation depends only on the values assigned to the variables in its scope. -/
theorem eval_congr {sem : Rel → List D → Bool} {c : Constraint Rel V} {σ τ : V → D}
    (h : ∀ v ∈ c.scope, σ v = τ v) :
    eval sem σ c = eval sem τ c :=
  congrArg (sem c.rel) (List.map_congr_left h)

end Constraint

namespace CSP

open Cslib.Complexity

variable {Rel V W D : Type*}

/-- Evaluate a CSP instance under assignment `σ : V → D`. -/
def eval (sem : Rel → List D → Bool) (σ : V → D) (F : CSP Rel V) : Bool :=
  F.all (Constraint.eval sem σ)

/-- A CSP instance is satisfiable if some assignment `σ : V → D` satisfies all its constraints. -/
def Satisfiable (sem : Rel → List D → Bool) (F : CSP Rel V) : Prop :=
  ∃ σ : V → D, F.eval sem σ = true

/-- All variable occurrences across the constraint scopes of `F`, in order. -/
def vars (F : CSP Rel V) : List V :=
  F.flatMap Constraint.scope

/-- Rename variables across all constraints in `F`. -/
def relabel (f : V → W) (F : CSP Rel V) : CSP Rel W :=
  F.map (Constraint.relabel f)

/-- Relabeling maps `CSP.vars` by the relabeling function. -/
@[simp]
theorem vars_relabel (f : V → W) (F : CSP Rel V) :
    (F.relabel f).vars = F.vars.map f := by
  simp [vars, relabel, Constraint.relabel, List.flatMap_map, List.map_flatMap]

/-- Evaluating a relabeled CSP instance composes the assignment with the relabeling. -/
@[simp]
theorem eval_relabel (sem : Rel → List D → Bool) (f : V → W) (σ : W → D) (F : CSP Rel V) :
    (F.relabel f).eval sem σ = F.eval sem (σ ∘ f) := by
  simp [eval, relabel, List.all_map, Function.comp_def]

/-- CSP evaluation depends only on the values assigned to its occurring variables `F.vars`. -/
theorem eval_congr {sem : Rel → List D → Bool} {F : CSP Rel V} {σ τ : V → D}
    (h : ∀ v ∈ F.vars, σ v = τ v) :
    F.eval sem σ = F.eval sem τ :=
  Bool.eq_iff_iff.mpr <| by
    simp only [eval, List.all_eq_true]
    exact forall₂_congr fun c hc => by
      rw [Constraint.eval_congr fun v hv => h v (List.mem_flatMap.mpr ⟨c, hc, hv⟩)]

/-- Auxiliary positive-clause CNF formula with the same variable-occurrence list `F.vars`. Used as a
proof device to transfer `CNF` variable-accounting and polynomial-time lemmas to `CSP`. -/
def varCNF (F : CSP Rel V) : CNF V :=
  F.map fun c => c.scope.map fun v => (v, true)

/-- The variable occurrences of `F.varCNF` are identical to `F.vars`. -/
@[simp]
theorem vars_varCNF (F : CSP Rel V) :
    (F.varCNF).vars = F.vars := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    simpa only [varCNF, List.map_cons, CNF.vars, List.flatten_cons, List.map_append,
      List.map_map, Function.comp_def, List.map_id', vars, List.flatMap_cons] using
      congrArg (c.scope ++ ·) ih

variable [DecidableEq V]

/-- Number of distinct variables occurring in `F`. -/
def numVars (F : CSP Rel V) : ℕ :=
  F.vars.toFinset.card

/-- Distinct variables of `F` in order of first occurrence. -/
def distinctVars (F : CSP Rel V) : List V :=
  selectDistinct F.vars (List.replicate F.vars.length true)

/-- `F.varCNF` has the same number of distinct variables as `F`. -/
@[simp]
theorem numVars_varCNF (F : CSP Rel V) :
    F.varCNF.numVars = F.numVars := by
  simp [CNF.numVars, numVars]

/-- `F.varCNF` has the same first-occurrence variable list as `F`. -/
@[simp]
theorem distinctVars_varCNF (F : CSP Rel V) :
    F.varCNF.distinctVars = F.distinctVars := by
  simp [CNF.distinctVars, distinctVars]

/-- A variable belongs to `F.distinctVars` iff it occurs in `F.vars`. -/
theorem mem_distinctVars {F : CSP Rel V} {v : V} :
    v ∈ F.distinctVars ↔ v ∈ F.vars :=
  mem_selectDistinct_replicate

/-- The length of `F.distinctVars` is `F.numVars`. -/
theorem length_distinctVars (F : CSP Rel V) :
    F.distinctVars.length = F.numVars :=
  length_selectDistinct_replicate F.vars

/-- Rename each variable occurring in `F` by its first-occurrence index in `F.distinctVars`. -/
def denseRelabel (F : CSP Rel V) : CSP Rel ℕ :=
  F.relabel F.distinctVars.idxOf

/-- The occurring variables of `F.denseRelabel` are `Finset.range F.numVars`. -/
@[simp]
theorem vars_denseRelabel_toFinset (F : CSP Rel V) :
    F.denseRelabel.vars.toFinset = Finset.range F.numVars := by
  have h := CNF.vars_dense_relabel F.varCNF
  simpa only [CNF.vars_relabel, vars_varCNF, distinctVars_varCNF, numVars_varCNF,
    denseRelabel, vars_relabel] using h

/-- Dense relabeling preserves the number of distinct occurring variables. -/
@[simp]
theorem numVars_denseRelabel (F : CSP Rel V) :
    F.denseRelabel.numVars = F.numVars := by
  rw [numVars, vars_denseRelabel_toFinset, Finset.card_range]

/-- Dense relabeling preserves any uniform upper bound on constraint scope lengths. -/
theorem all_length_le_denseRelabel {k : ℕ} (F : CSP Rel V) :
    (∀ c ∈ F.denseRelabel, c.scope.length ≤ k) ↔ ∀ c ∈ F, c.scope.length ≤ k := by
  simp [denseRelabel, relabel, Constraint.relabel]

/-- Count assignments to `declared : Finset V` (extended by `default` outside `declared`) that
satisfy `F` under `sem`. -/
def modelCountOn [Fintype D] [Inhabited D] (sem : Rel → List D → Bool) (F : CSP Rel V)
    (declared : Finset V) : ℕ :=
  (Finset.univ.filter fun σ : declared → D =>
    F.eval sem (fun v => if h : v ∈ declared then σ ⟨v, h⟩ else default) = true).card

/-- Count satisfying assignments on the occurring variables `F.vars.toFinset`. -/
def modelCount [Fintype D] [Inhabited D] (sem : Rel → List D → Bool) (F : CSP Rel V) : ℕ :=
  F.modelCountOn sem F.vars.toFinset

/-- Dense variable relabeling preserves the occurring-variable model count on
`Finset.range F.numVars`. -/
theorem modelCountOn_denseRelabel [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : CSP Rel V) :
    F.denseRelabel.modelCountOn sem (Finset.range F.numVars) = F.modelCount sem := by
  classical
  let S := F.vars.toFinset
  let R := Finset.range F.numVars
  let f : S → R := fun v => ⟨F.distinctVars.idxOf v.val, Finset.mem_range.mpr
    (F.length_distinctVars ▸ List.idxOf_lt_length_iff.mpr
      (mem_distinctVars.mpr (List.mem_toFinset.mp v.property)))⟩
  let eVar : S ≃ R := Equiv.ofBijective f
    ⟨fun v w h => Subtype.ext ((List.idxOf_inj
        (mem_distinctVars.mpr (List.mem_toFinset.mp v.property))).mp (Subtype.mk.inj h)),
      fun i => by
        have hi : i.val ∈ F.denseRelabel.vars.toFinset :=
          F.vars_denseRelabel_toFinset.symm ▸ i.property
        rw [denseRelabel, vars_relabel, List.mem_toFinset, List.mem_map] at hi
        obtain ⟨v, hv, hvi⟩ := hi
        exact ⟨⟨v, List.mem_toFinset.mpr hv⟩, Subtype.ext hvi⟩⟩
  rw [modelCount, modelCountOn, modelCountOn]
  refine Finset.card_equiv (eVar.symm.arrowCongr (Equiv.refl D)) fun σ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine Eq.congr_left ?_
  rw [denseRelabel, eval_relabel]
  refine eval_congr fun v hv => ?_
  have hidx : List.idxOf v F.distinctVars ∈ Finset.range F.numVars :=
    (f ⟨v, List.mem_toFinset.mpr hv⟩).property
  simp only [Function.comp_apply, List.mem_toFinset.mpr hv, hidx, dite_true]
  rfl

/-- Dense variable relabeling preserves `CSP.modelCount`. -/
@[simp]
theorem modelCount_denseRelabel [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : CSP Rel V) :
    F.denseRelabel.modelCount sem = F.modelCount sem := by
  rw [modelCount, vars_denseRelabel_toFinset, modelCountOn_denseRelabel]

/-- A CSP instance is satisfiable if and only if its model count is positive. -/
theorem modelCount_pos_iff [Fintype D] [Inhabited D] {sem : Rel → List D → Bool} {F : CSP Rel V} :
    0 < F.modelCount sem ↔ F.Satisfiable sem := by
  rw [modelCount, modelCountOn, Finset.card_pos, Finset.filter_nonempty_iff]
  refine ⟨fun ⟨_, _, hσ⟩ => ⟨_, hσ⟩, fun ⟨σ, hσ⟩ => ⟨fun v => σ v.val, Finset.mem_univ _, ?_⟩⟩
  exact (eval_congr fun v hv => by simp [List.mem_toFinset.mpr hv]).trans hσ

/-- Guard checking that every constraint scope in `F` has length `≤ k` and every occurring variable
lies in `< N`. -/
def validDeclaredCSP (k N : ℕ) (F : CSP Rel ℕ) : Bool :=
  (F.all fun c => decide (c.scope.length ≤ k)) && (F.vars.all fun v => decide (v < N))

/-- `validDeclaredCSP k N F` holds iff every constraint scope has length `≤ k` and all occurring
variables lie in `Finset.range N`. -/
theorem validDeclaredCSP_eq_true_iff {k N : ℕ} {F : CSP Rel ℕ} :
    validDeclaredCSP k N F = true ↔
      (∀ c ∈ F, c.scope.length ≤ k) ∧ F.vars.toFinset ⊆ Finset.range N := by
  simp only [validDeclaredCSP, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact and_congr_right' ⟨fun h _ hv => Finset.mem_range.mpr (h _ (List.mem_toFinset.mp hv)),
    fun h _ hv => Finset.mem_range.mp (h (List.mem_toFinset.mpr hv))⟩

/-- The bounded-arity CSP decision problem over relation semantics `sem`. -/
def KCSP (k : ℕ) (sem : Rel → List D → Bool) : Set (CSP Rel V) :=
  {F | (∀ c ∈ F, c.scope.length ≤ k) ∧ F.Satisfiable sem}

end CSP

end Cslib.Logic.PL
