/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Eval
public import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF
public import CslibFrontier.Logics.Propositional.TseitinCNF
public import Mathlib.Order.WithBot

/-!
# Weighted partial MaxSAT and propositional translations

A weighted partial MaxSAT instance (`Cslib.Logic.PL.MaxSAT`) pairs hard clauses `hard : CNF V`
with weighted soft clauses `soft : List (Clause V × ℕ)` (repeated soft clauses are counted with
their multiplicity). An assignment is feasible when it satisfies `hard`, and its cost is the sum
of weights of falsified soft clauses. The optimum (`MaxSAT.optimum`) is the least cost of a
feasible assignment in `WithTop ℕ`, or `⊤` when the hard clauses are unsatisfiable.
Equivalently, `MaxSAT.maxSatisfiedWeight` gives the maximum weight of simultaneously satisfied
soft clauses in `WithBot ℕ`.

For arbitrary propositions (`Cslib.Logic.PL.PropMaxSAT`), the Tseitin translation
(`PropMaxSAT.toTseitin`) and positive-polarity Plaisted–Greenbaum translation
(`PropMaxSAT.toPlaistedGreenbaum`) produce clausal weighted partial MaxSAT instances with linearly
many clauses, clause width at most three, and the same optimum cost:

* In `PropMaxSAT.toTseitin`, feasible assignments correspond bijectively (on the variables of the
  translation) via restriction and `Proposition.tseitinExtend`, with identical cost.
* In `PropMaxSAT.toPlaistedGreenbaum`, feasible source assignments extend via
  `Proposition.tseitinExtend` with equal cost, while every feasible assignment of the translation
  restricts to a feasible assignment of at most the same cost.

## Main definitions

* `Cslib.Logic.PL.MaxSAT`, `Cslib.Logic.PL.MaxSAT.feasible`, `Cslib.Logic.PL.MaxSAT.cost`,
  `Cslib.Logic.PL.MaxSAT.optimum`, `Cslib.Logic.PL.MaxSAT.maxSatisfiedWeight`.
* `Cslib.Logic.PL.MaxSAT.HasCostAtMost`, `Cslib.Logic.PL.MaxSAT.HasSatisfiedWeightAtLeast`.
* `Cslib.Logic.PL.MaxSAT.unweighted`, `Cslib.Logic.PL.MaxSAT.relabel`,
  `Cslib.Logic.PL.MaxSAT.computeOptimum`.
* `Cslib.Logic.PL.PropMaxSAT`, `Cslib.Logic.PL.PropMaxSAT.toTseitin`,
  `Cslib.Logic.PL.PropMaxSAT.toPlaistedGreenbaum`.

## References

* [F. Bacchus, M. Järvisalo, R. Martins, *Maximum Satisfiability*][BacchusJarvisaloMartins2021]
  (primary PDF unverified)
* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
* [D. A. Plaisted, S. Greenbaum, *A structure-preserving clause form
  translation*][PlaistedGreenbaum1986]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Classical in
private lemma list_sum_map_le_sum_map {α : Type*} (l : List α) (f g : α → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx))

private lemma list_sum_map_add_sum_map {α : Type*} (l : List α) (f g : α → ℕ) :
    (l.map f).sum + (l.map g).sum = (l.map fun x => f x + g x).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ### Clausal weighted partial MaxSAT -/

/-- A weighted partial MaxSAT instance over variable type `V`. Repeated soft clauses are counted
with multiplicity. -/
@[ext]
structure MaxSAT (V : Type*) where
  /-- Clauses that must be satisfied by every feasible assignment. -/
  hard : CNF V
  /-- Soft clauses paired with non-negative integer weights. -/
  soft : List (Clause V × ℕ)

namespace MaxSAT

variable {V : Type*}

/-- An assignment is feasible when it satisfies every hard clause. -/
def feasible (φ : MaxSAT V) (σ : V → Bool) : Prop :=
  φ.hard.eval σ = true

/-- Total weight of soft clauses falsified by `σ`. -/
def cost (φ : MaxSAT V) (σ : V → Bool) : ℕ :=
  (φ.soft.map fun cw => if cw.1.eval σ then 0 else cw.2).sum

/-- Total weight of all soft clauses in `φ`. -/
def totalWeight (φ : MaxSAT V) : ℕ :=
  (φ.soft.map Prod.snd).sum

/-- Total weight of soft clauses satisfied by `σ`. -/
def satisfiedWeight (φ : MaxSAT V) (σ : V → Bool) : ℕ :=
  (φ.soft.map fun cw => if cw.1.eval σ then cw.2 else 0).sum

/-- The underlying soft clauses as a CNF list. -/
def softClauses (φ : MaxSAT V) : CNF V :=
  φ.soft.map Prod.fst

/-- All variable occurrences appearing in the hard or soft clauses of `φ`. -/
def vars (φ : MaxSAT V) : List V :=
  φ.hard.vars ++ φ.softClauses.vars

theorem cost_add_satisfiedWeight (φ : MaxSAT V) (σ : V → Bool) :
    φ.cost σ + φ.satisfiedWeight σ = φ.totalWeight := by
  unfold cost satisfiedWeight totalWeight
  rw [list_sum_map_add_sum_map]
  congr 1
  refine List.map_congr_left fun cw _ => ?_
  cases cw.1.eval σ <;> simp

theorem cost_le_totalWeight (φ : MaxSAT V) (σ : V → Bool) : φ.cost σ ≤ φ.totalWeight := by
  have h := φ.cost_add_satisfiedWeight σ
  omega

theorem satisfiedWeight_le_totalWeight (φ : MaxSAT V) (σ : V → Bool) :
    φ.satisfiedWeight σ ≤ φ.totalWeight := by
  have h := φ.cost_add_satisfiedWeight σ
  omega

theorem satisfiedWeight_eq_totalWeight_sub_cost (φ : MaxSAT V) (σ : V → Bool) :
    φ.satisfiedWeight σ = φ.totalWeight - φ.cost σ := by
  have h := φ.cost_add_satisfiedWeight σ
  omega

theorem cost_eq_totalWeight_sub_satisfiedWeight (φ : MaxSAT V) (σ : V → Bool) :
    φ.cost σ = φ.totalWeight - φ.satisfiedWeight σ := by
  have h := φ.cost_add_satisfiedWeight σ
  omega

theorem feasible_congr {φ : MaxSAT V} {σ τ : V → Bool}
    (h : ∀ v ∈ φ.vars, σ v = τ v) : φ.feasible σ ↔ φ.feasible τ := by
  have heq : φ.hard.eval σ = φ.hard.eval τ :=
    CNF.eval_congr fun v hv => h v (List.mem_append_left _ hv)
  simp only [feasible, heq]

theorem cost_congr {φ : MaxSAT V} {σ τ : V → Bool}
    (h : ∀ v ∈ φ.vars, σ v = τ v) : φ.cost σ = φ.cost τ := by
  unfold cost
  congr 1
  refine List.map_congr_left fun cw hcw => ?_
  have hcl : cw.1.eval σ = cw.1.eval τ := Clause.eval_congr fun l hl => by
    refine h l.1 (List.mem_append_right _ (CNF.mem_vars.2 ?_))
    exact ⟨cw.1, List.mem_map.2 ⟨cw, hcw, rfl⟩, l.2, hl⟩
  rw [hcl]

theorem satisfiedWeight_congr {φ : MaxSAT V} {σ τ : V → Bool}
    (h : ∀ v ∈ φ.vars, σ v = τ v) : φ.satisfiedWeight σ = φ.satisfiedWeight τ := by
  have hc := cost_congr h
  have hs := φ.cost_add_satisfiedWeight σ
  have ht := φ.cost_add_satisfiedWeight τ
  omega

/-- Minimum cost among feasible assignments of `φ`, or `⊤` when `φ.hard` is unsatisfiable. -/
noncomputable def optimum (φ : MaxSAT V) : WithTop ℕ :=
  open Classical in
  if h : ∃ σ : V → Bool, φ.feasible σ then
    ((Nat.find (⟨φ.cost h.choose, h.choose, h.choose_spec, rfl⟩ :
      ∃ k : ℕ, ∃ σ : V → Bool, φ.feasible σ ∧ φ.cost σ = k) : ℕ) : WithTop ℕ)
  else ⊤

theorem optimum_eq_top_iff (φ : MaxSAT V) : φ.optimum = ⊤ ↔ ¬ φ.hard.Satisfiable := by
  classical
  unfold optimum
  split_ifs with h
  · simpa [feasible, CNF.Satisfiable, WithTop.coe_ne_top] using h
  · simpa [feasible, CNF.Satisfiable] using h

theorem optimum_ne_top_iff (φ : MaxSAT V) : φ.optimum ≠ ⊤ ↔ φ.hard.Satisfiable := by
  rw [ne_eq, optimum_eq_top_iff, not_not]

/-- **Attainment of the minimum**: every satisfiable MaxSAT instance has a feasible assignment
achieving `φ.optimum`. -/
theorem exists_feasible_cost_eq_optimum {φ : MaxSAT V} (h : φ.hard.Satisfiable) :
    ∃ σ : V → Bool, φ.feasible σ ∧ (φ.cost σ : WithTop ℕ) = φ.optimum := by
  classical
  have h' : ∃ σ : V → Bool, φ.feasible σ := h
  unfold optimum
  rw [dite_eq_left h']
  obtain ⟨σ, hσ, hcost⟩ :=
    Nat.find_spec (⟨φ.cost h'.choose, h'.choose, h'.choose_spec, rfl⟩ :
      ∃ k : ℕ, ∃ σ : V → Bool, φ.feasible σ ∧ φ.cost σ = k)
  exact ⟨σ, hσ, congrArg ((↑) : ℕ → WithTop ℕ) hcost⟩

/-- **Finite-support attainment**: when `φ.hard` is satisfiable, the minimum cost is achieved by
an assignment that takes `false` on every variable outside `φ.vars`. -/
theorem exists_feasible_cost_eq_optimum_support {φ : MaxSAT V} (h : φ.hard.Satisfiable) :
    ∃ σ : V → Bool, (∀ v ∉ φ.vars, σ v = false) ∧
      φ.feasible σ ∧ (φ.cost σ : WithTop ℕ) = φ.optimum := by
  classical
  obtain ⟨σ, hfeas, hopt⟩ := exists_feasible_cost_eq_optimum h
  let τ : V → Bool := fun v => if v ∈ φ.vars then σ v else false
  have hagree : ∀ v ∈ φ.vars, τ v = σ v := fun v hv => by simp [τ, hv]
  refine ⟨τ, fun v hv => by simp [τ, hv], (feasible_congr hagree).2 hfeas, ?_⟩
  rw [cost_congr hagree, hopt]

theorem optimum_le_cost {φ : MaxSAT V} {σ : V → Bool} (hσ : φ.feasible σ) :
    φ.optimum ≤ (φ.cost σ : WithTop ℕ) := by
  classical
  have h' : ∃ σ : V → Bool, φ.feasible σ := ⟨σ, hσ⟩
  unfold optimum
  rw [dite_eq_left h']
  exact WithTop.coe_le_coe.2 (Nat.find_min' _ ⟨σ, hσ, rfl⟩)

theorem le_optimum_iff {φ : MaxSAT V} {k : ℕ} :
    (k : WithTop ℕ) ≤ φ.optimum ↔ ∀ σ : V → Bool, φ.feasible σ → k ≤ φ.cost σ := by
  refine ⟨fun hk σ hσ => WithTop.coe_le_coe.1 (hk.trans (optimum_le_cost hσ)), fun hk => ?_⟩
  by_cases hsat : φ.hard.Satisfiable
  · obtain ⟨σ, hσ, hopt⟩ := exists_feasible_cost_eq_optimum hsat
    rw [← hopt]
    exact WithTop.coe_le_coe.2 (hk σ hσ)
  · rw [φ.optimum_eq_top_iff.2 hsat]
    exact le_top

theorem optimum_le_iff {φ : MaxSAT V} {k : ℕ} :
    φ.optimum ≤ (k : WithTop ℕ) ↔ ∃ σ : V → Bool, φ.feasible σ ∧ φ.cost σ ≤ k := by
  refine ⟨fun hk => ?_, fun ⟨σ, hσ, hcost⟩ =>
    (optimum_le_cost hσ).trans (WithTop.coe_le_coe.2 hcost)⟩
  have hne : φ.optimum ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hk (WithTop.coe_lt_top k))
  obtain ⟨σ, hσ, hopt⟩ := exists_feasible_cost_eq_optimum (φ.optimum_ne_top_iff.1 hne)
  exact ⟨σ, hσ, WithTop.coe_le_coe.1 (hopt ▸ hk)⟩

theorem optimum_eq_coe_iff {φ : MaxSAT V} {k : ℕ} :
    φ.optimum = (k : WithTop ℕ) ↔
      (∃ σ : V → Bool, φ.feasible σ ∧ φ.cost σ = k) ∧
        (∀ σ : V → Bool, φ.feasible σ → k ≤ φ.cost σ) := by
  refine ⟨fun h => ?_, fun ⟨⟨σ, hσ, hc⟩, hmin⟩ =>
    le_antisymm ((optimum_le_cost hσ).trans (by rw [hc])) (le_optimum_iff.2 hmin)⟩
  have hne : φ.optimum ≠ ⊤ := by simp [h, WithTop.coe_ne_top]
  obtain ⟨σ, hσ, hopt⟩ := exists_feasible_cost_eq_optimum (φ.optimum_ne_top_iff.1 hne)
  exact ⟨⟨σ, hσ, WithTop.coe_eq_coe.1 (hopt.trans h)⟩, le_optimum_iff.1 h.ge⟩

theorem optimum_le_totalWeight_of_satisfiable {φ : MaxSAT V} (h : φ.hard.Satisfiable) :
    φ.optimum ≤ (φ.totalWeight : WithTop ℕ) := by
  obtain ⟨σ, hσ⟩ := h
  exact (optimum_le_cost hσ).trans (WithTop.coe_le_coe.2 (φ.cost_le_totalWeight σ))

theorem optimum_le_optimum_of_forall {W : Type*} {φ : MaxSAT V} {ψ : MaxSAT W}
    (h : ∀ τ : W → Bool, ψ.feasible τ → ∃ σ : V → Bool, φ.feasible σ ∧ φ.cost σ ≤ ψ.cost τ) :
    φ.optimum ≤ ψ.optimum := by
  by_cases hsat : ψ.hard.Satisfiable
  · obtain ⟨τ, hτ, hopt⟩ := exists_feasible_cost_eq_optimum hsat
    obtain ⟨σ, hσ, hle⟩ := h τ hτ
    exact (optimum_le_cost hσ).trans ((WithTop.coe_le_coe.2 hle).trans_eq hopt)
  · rw [ψ.optimum_eq_top_iff.2 hsat]
    exact le_top

/-! ### Decision version and maximum satisfied weight -/

/-- The cost decision problem: `φ` admits a feasible assignment of cost at most `k`. -/
def HasCostAtMost (φ : MaxSAT V) (k : ℕ) : Prop :=
  ∃ σ : V → Bool, φ.feasible σ ∧ φ.cost σ ≤ k

theorem hasCostAtMost_iff_optimum_le {φ : MaxSAT V} {k : ℕ} :
    φ.HasCostAtMost k ↔ φ.optimum ≤ (k : WithTop ℕ) :=
  optimum_le_iff.symm

/-- The satisfied-weight decision problem: `φ` admits a feasible assignment satisfying weight at
least `t`. -/
def HasSatisfiedWeightAtLeast (φ : MaxSAT V) (t : ℕ) : Prop :=
  ∃ σ : V → Bool, φ.feasible σ ∧ t ≤ φ.satisfiedWeight σ

theorem hasSatisfiedWeightAtLeast_iff {φ : MaxSAT V} {t : ℕ} :
    φ.HasSatisfiedWeightAtLeast t ↔
      t ≤ φ.totalWeight ∧ φ.HasCostAtMost (φ.totalWeight - t) := by
  constructor
  · rintro ⟨σ, hσ, ht⟩
    have hsum := φ.cost_add_satisfiedWeight σ
    exact ⟨ht.trans (φ.satisfiedWeight_le_totalWeight σ), ⟨σ, hσ, by omega⟩⟩
  · rintro ⟨ht, ⟨σ, hσ, hc⟩⟩
    have hsum := φ.cost_add_satisfiedWeight σ
    exact ⟨σ, hσ, by omega⟩

/-- Maximum weight of soft clauses simultaneously satisfied by a feasible assignment, or `⊥` when
`φ.hard` is unsatisfiable. -/
noncomputable def maxSatisfiedWeight (φ : MaxSAT V) : WithBot ℕ :=
  match φ.optimum with
  | ⊤ => ⊥
  | (k : ℕ) => ((φ.totalWeight - k : ℕ) : WithBot ℕ)

theorem maxSatisfiedWeight_eq_bot_iff (φ : MaxSAT V) :
    φ.maxSatisfiedWeight = ⊥ ↔ ¬ φ.hard.Satisfiable := by
  unfold maxSatisfiedWeight
  cases h : φ.optimum with
  | top => simpa [WithTop.none_eq_top] using φ.optimum_eq_top_iff.1 h
  | coe k =>
    have hne : φ.optimum ≠ ⊤ := by simp [h, WithTop.coe_ne_top]
    simpa [WithTop.some_eq_coe, WithBot.coe_ne_bot] using φ.optimum_ne_top_iff.1 hne

theorem satisfiedWeight_le_maxSatisfiedWeight {φ : MaxSAT V} {σ : V → Bool} (hσ : φ.feasible σ) :
    (φ.satisfiedWeight σ : WithBot ℕ) ≤ φ.maxSatisfiedWeight := by
  unfold maxSatisfiedWeight
  have hne : φ.optimum ≠ ⊤ := φ.optimum_ne_top_iff.2 ⟨σ, hσ⟩
  cases h : φ.optimum with
  | top => exact absurd h hne
  | coe k =>
    have hk : k ≤ φ.cost σ := WithTop.coe_le_coe.1 (h ▸ optimum_le_cost hσ)
    have hsum := φ.cost_add_satisfiedWeight σ
    exact WithBot.coe_le_coe.2 (by omega)

theorem exists_feasible_satisfiedWeight_eq_maxSatisfiedWeight {φ : MaxSAT V}
    (h : φ.hard.Satisfiable) :
    ∃ σ : V → Bool, φ.feasible σ ∧ (φ.satisfiedWeight σ : WithBot ℕ) = φ.maxSatisfiedWeight := by
  obtain ⟨σ, hσ, hopt⟩ := exists_feasible_cost_eq_optimum h
  refine ⟨σ, hσ, ?_⟩
  unfold maxSatisfiedWeight
  rw [← hopt, φ.satisfiedWeight_eq_totalWeight_sub_cost σ]

theorem le_maxSatisfiedWeight_iff {φ : MaxSAT V} {t : ℕ} :
    (t : WithBot ℕ) ≤ φ.maxSatisfiedWeight ↔ φ.HasSatisfiedWeightAtLeast t := by
  constructor
  · intro ht
    have hne : φ.maxSatisfiedWeight ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe t) ht)
    have hsat : φ.hard.Satisfiable := not_not.1 (φ.maxSatisfiedWeight_eq_bot_iff.not.1 hne)
    obtain ⟨σ, hσ, hmax⟩ := exists_feasible_satisfiedWeight_eq_maxSatisfiedWeight hsat
    exact ⟨σ, hσ, WithBot.coe_le_coe.1 (ht.trans_eq hmax.symm)⟩
  · rintro ⟨σ, hσ, ht⟩
    exact (WithBot.coe_le_coe.2 ht).trans (satisfiedWeight_le_maxSatisfiedWeight hσ)

theorem maxSatisfiedWeight_eq_coe_iff {φ : MaxSAT V} {t : ℕ} :
    φ.maxSatisfiedWeight = (t : WithBot ℕ) ↔
      (∃ σ : V → Bool, φ.feasible σ ∧ φ.satisfiedWeight σ = t) ∧
        (∀ σ : V → Bool, φ.feasible σ → φ.satisfiedWeight σ ≤ t) := by
  constructor
  · intro h
    have hne : φ.maxSatisfiedWeight ≠ ⊥ := by simp [h, WithBot.coe_ne_bot]
    have hsat : φ.hard.Satisfiable := not_not.1 (φ.maxSatisfiedWeight_eq_bot_iff.not.1 hne)
    obtain ⟨σ, hσ, hmax⟩ := exists_feasible_satisfiedWeight_eq_maxSatisfiedWeight hsat
    exact ⟨⟨σ, hσ, WithBot.coe_eq_coe.1 (hmax.trans h)⟩,
      fun τ hτ => WithBot.coe_le_coe.1 ((satisfiedWeight_le_maxSatisfiedWeight hτ).trans_eq h)⟩
  · rintro ⟨⟨σ, hσ, hs⟩, hle⟩
    exact le_antisymm
      (by
        by_cases hsat : φ.hard.Satisfiable
        · obtain ⟨τ, hτ, hmax⟩ := exists_feasible_satisfiedWeight_eq_maxSatisfiedWeight hsat
          rw [← hmax]
          exact WithBot.coe_le_coe.2 (hle τ hτ)
        · rw [φ.maxSatisfiedWeight_eq_bot_iff.2 hsat]
          exact bot_le)
      ((WithBot.coe_le_coe.2 hs.ge).trans (satisfiedWeight_le_maxSatisfiedWeight hσ))

theorem optimum_add_maxSatisfiedWeight {φ : MaxSAT V} (h : φ.hard.Satisfiable) :
    ∃ opt maxSat : ℕ,
      φ.optimum = (opt : WithTop ℕ) ∧
        φ.maxSatisfiedWeight = (maxSat : WithBot ℕ) ∧
        opt + maxSat = φ.totalWeight := by
  obtain ⟨σ, hσ, hopt⟩ := exists_feasible_cost_eq_optimum h
  refine ⟨φ.cost σ, φ.satisfiedWeight σ, hopt.symm, ?_, φ.cost_add_satisfiedWeight σ⟩
  unfold maxSatisfiedWeight
  rw [← hopt, φ.satisfiedWeight_eq_totalWeight_sub_cost σ]

/-! ### Computable solver over finite variable lists -/

/-- Branch-and-enumerate optimum over a finite list `vs` of variables, starting from base
assignment `σ`. -/
def optimumOn [DecidableEq V] (φ : MaxSAT V) : List V → (V → Bool) → WithTop ℕ
  | [], σ => if φ.hard.eval σ then (φ.cost σ : WithTop ℕ) else ⊤
  | v :: vs, σ =>
      min (φ.optimumOn vs (fun w => if w = v then true else σ w))
          (φ.optimumOn vs (fun w => if w = v then false else σ w))

private theorem optimumOn_le_of_agree [DecidableEq V] (φ : MaxSAT V) (vs : List V)
    (σ τ : V → Bool) (hτ : φ.feasible τ) (hout : ∀ w, w ∉ vs → τ w = σ w) :
    φ.optimumOn vs σ ≤ (φ.cost τ : WithTop ℕ) := by
  induction vs generalizing σ with
  | nil =>
    have heq : τ = σ := funext fun w => hout w List.not_mem_nil
    simp only [optimumOn, heq]
    split_ifs with h'
    · exact le_rfl
    · exact absurd (heq ▸ hτ) h'
  | cons v vs ih =>
    simp only [optimumOn]
    have hnot : ∀ w, w ∉ vs → w ≠ v → τ w = σ w := fun w hw hne =>
      hout w fun hm => by
        rcases List.mem_cons.1 hm with rfl | hm
        · exact hne rfl
        · exact hw hm
    cases hv : τ v
    · refine min_le_of_right_le (ih (fun w => if w = v then false else σ w) fun w hw => ?_)
      by_cases hweq : w = v
      · simp [hweq, hv]
      · simp [hweq, hnot w hw hweq]
    · refine min_le_of_left_le (ih (fun w => if w = v then true else σ w) fun w hw => ?_)
      by_cases hweq : w = v
      · simp [hweq, hv]
      · simp [hweq, hnot w hw hweq]

private theorem optimumOn_witness_or_top [DecidableEq V] (φ : MaxSAT V) (vs : List V)
    (σ : V → Bool) :
    φ.optimumOn vs σ = ⊤ ∨
      ∃ τ : V → Bool, (∀ w, w ∉ vs → τ w = σ w) ∧
        φ.feasible τ ∧ φ.optimumOn vs σ = (φ.cost τ : WithTop ℕ) := by
  induction vs generalizing σ with
  | nil =>
    simp only [optimumOn]
    split_ifs with h
    · exact .inr ⟨σ, fun _ _ => rfl, h, rfl⟩
    · exact .inl rfl
  | cons v vs ih =>
    simp only [optimumOn]
    set σt : V → Bool := fun w => if w = v then true else σ w
    set σf : V → Bool := fun w => if w = v then false else σ w
    rcases le_total (φ.optimumOn vs σt) (φ.optimumOn vs σf) with hle | hle
    · rw [min_eq_left hle]
      rcases ih σt with ht | ⟨τ, hout, hfeas, hcost⟩
      · exact .inl ht
      · refine .inr ⟨τ, fun w hw => ?_, hfeas, hcost⟩
        have hnotvs : w ∉ vs := fun hm => hw (List.mem_cons_of_mem v hm)
        have hne : w ≠ v := fun heq => hw (heq ▸ List.mem_cons_self)
        simpa [σt, hne] using hout w hnotvs
    · rw [min_eq_right hle]
      rcases ih σf with hf | ⟨τ, hout, hfeas, hcost⟩
      · exact .inl hf
      · refine .inr ⟨τ, fun w hw => ?_, hfeas, hcost⟩
        have hnotvs : w ∉ vs := fun hm => hw (List.mem_cons_of_mem v hm)
        have hne : w ≠ v := fun heq => hw (heq ▸ List.mem_cons_self)
        simpa [σf, hne] using hout w hnotvs

/-- When `vs` contains every variable occurring in `φ`, `φ.optimumOn vs σ` computes `φ.optimum`.
-/
theorem optimumOn_eq_optimum [DecidableEq V] (φ : MaxSAT V) (vs : List V)
    (hvars : ∀ v ∈ φ.vars, v ∈ vs) (σ : V → Bool) :
    φ.optimumOn vs σ = φ.optimum := by
  rcases optimumOn_witness_or_top φ vs σ with htop | ⟨τ, _, hfeas, hcost⟩
  · have hunsat : ¬ φ.hard.Satisfiable := by
      rintro ⟨ρ, hρ⟩
      let ρ' : V → Bool := fun w => if w ∈ vs then ρ w else σ w
      have hagree : ∀ w ∈ φ.vars, ρ' w = ρ w := fun w hw => by simp [ρ', hvars w hw]
      have hρ' : φ.feasible ρ' := (feasible_congr hagree).2 hρ
      have hle := optimumOn_le_of_agree φ vs σ ρ' hρ' (fun w hw => by simp [ρ', hw])
      rw [htop, top_le_iff] at hle
      exact absurd hle (by simp)
    rw [htop, φ.optimum_eq_top_iff.2 hunsat]
  · refine le_antisymm ?_ (hcost ▸ optimum_le_cost hfeas)
    by_cases hsat : φ.hard.Satisfiable
    · obtain ⟨ρ, hρ, hopt⟩ := exists_feasible_cost_eq_optimum hsat
      let ρ' : V → Bool := fun w => if w ∈ vs then ρ w else σ w
      have hagree : ∀ w ∈ φ.vars, ρ' w = ρ w := fun w hw => by simp [ρ', hvars w hw]
      have hle := optimumOn_le_of_agree φ vs σ ρ' ((feasible_congr hagree).2 hρ)
        (fun w hw => by simp [ρ', hw])
      rwa [cost_congr hagree, hopt] at hle
    · rw [φ.optimum_eq_top_iff.2 hsat]
      exact le_top

/-- Deduplicate a list of variables, preserving membership. -/
def dedupVars [DecidableEq V] : List V → List V
  | [] => []
  | v :: vs => if v ∈ vs then dedupVars vs else v :: dedupVars vs

theorem mem_dedupVars [DecidableEq V] {xs : List V} {v : V} : v ∈ dedupVars xs ↔ v ∈ xs := by
  induction xs with
  | nil => simp [dedupVars]
  | cons a xs ih =>
    simp only [dedupVars]
    split_ifs with ha
    · rw [ih]
      constructor
      · exact List.mem_cons_of_mem a
      · intro hv
        rcases List.mem_cons.1 hv with rfl | hv'
        · exact ha
        · exact hv'
    · simp only [List.mem_cons, ih]

/-- Computable optimum for instances with decidable variable equality, suitable for `decide`. -/
def computeOptimum [DecidableEq V] (φ : MaxSAT V) : WithTop ℕ :=
  φ.optimumOn (dedupVars φ.vars) (fun _ => false)

theorem computeOptimum_eq_optimum [DecidableEq V] (φ : MaxSAT V) :
    φ.computeOptimum = φ.optimum :=
  optimumOn_eq_optimum φ (dedupVars φ.vars) (fun _ hv => mem_dedupVars.2 hv) _

/-! ### Basic theory: empty soft, unweighted, relabelling, and monotonicity -/

theorem optimum_soft_nil_eq_zero_iff (h : CNF V) :
    ({ hard := h, soft := [] } : MaxSAT V).optimum = ((0 : ℕ) : WithTop ℕ) ↔ h.Satisfiable := by
  constructor
  · intro heq
    have hne : ({ hard := h, soft := [] } : MaxSAT V).optimum ≠ ⊤ := by
      rw [heq]
      exact WithTop.coe_ne_top
    exact (optimum_ne_top_iff _).1 hne
  · intro ⟨σ, hσ⟩
    exact optimum_eq_coe_iff.2 ⟨⟨σ, hσ, by simp [cost]⟩, fun _ _ => Nat.zero_le _⟩

theorem optimum_soft_nil_eq_top_iff (h : CNF V) :
    ({ hard := h, soft := [] } : MaxSAT V).optimum = ⊤ ↔ ¬ h.Satisfiable :=
  optimum_eq_top_iff _

/-- Unweighted MaxSAT view of a CNF formula: no hard clauses, each clause given unit weight. -/
def unweighted (φ : CNF V) : MaxSAT V where
  hard := []
  soft := φ.map (·, 1)

@[simp]
theorem feasible_unweighted (φ : CNF V) (σ : V → Bool) : (unweighted φ).feasible σ := by
  simp [unweighted, feasible]

@[simp]
theorem totalWeight_unweighted (φ : CNF V) : (unweighted φ).totalWeight = φ.length := by
  simp [unweighted, totalWeight, List.map_map, Function.comp_def]

theorem cost_unweighted (φ : CNF V) (σ : V → Bool) :
    (unweighted φ).cost σ = φ.countUnsat σ := by
  unfold cost unweighted CNF.countUnsat
  induction φ with
  | nil => simp
  | cons c φ ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    cases c.eval σ <;> simp [Nat.add_comm]

theorem satisfiedWeight_unweighted (φ : CNF V) (σ : V → Bool) :
    (unweighted φ).satisfiedWeight σ = φ.countP (Clause.eval σ) := by
  unfold satisfiedWeight unweighted
  induction φ with
  | nil => simp
  | cons c φ ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    cases c.eval σ <;> simp [Nat.add_comm]

theorem optimum_unweighted_ne_top (φ : CNF V) : (unweighted φ).optimum ≠ ⊤ :=
  (optimum_ne_top_iff _).2 ⟨fun _ => false, by simp [unweighted]⟩

theorem optimum_unweighted_eq_zero_iff (φ : CNF V) :
    (unweighted φ).optimum = ((0 : ℕ) : WithTop ℕ) ↔ φ.Satisfiable := by
  rw [optimum_eq_coe_iff]
  constructor
  · rintro ⟨⟨σ, -, hcost⟩, -⟩
    rw [cost_unweighted, CNF.countUnsat_eq_zero_iff] at hcost
    exact ⟨σ, hcost⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨⟨σ, feasible_unweighted φ σ, ?_⟩, fun _ _ => Nat.zero_le _⟩
    rwa [cost_unweighted, CNF.countUnsat_eq_zero_iff]

/-- Rename all variables of a MaxSAT instance along `f : V → W`, reusing `CNF.relabel`. -/
def relabel {W : Type*} (f : V → W) (φ : MaxSAT V) : MaxSAT W where
  hard := φ.hard.relabel f
  soft := φ.soft.map fun cw => (cw.1.relabel f, cw.2)

@[simp]
theorem feasible_relabel {W : Type*} (f : V → W) (φ : MaxSAT V) (τ : W → Bool) :
    (φ.relabel f).feasible τ ↔ φ.feasible (τ ∘ f) := by
  simp [feasible, relabel]

@[simp]
theorem cost_relabel {W : Type*} (f : V → W) (φ : MaxSAT V) (τ : W → Bool) :
    (φ.relabel f).cost τ = φ.cost (τ ∘ f) := by
  simp [cost, relabel, List.map_map, Function.comp_def]

@[simp]
theorem satisfiedWeight_relabel {W : Type*} (f : V → W) (φ : MaxSAT V) (τ : W → Bool) :
    (φ.relabel f).satisfiedWeight τ = φ.satisfiedWeight (τ ∘ f) := by
  simp [satisfiedWeight, relabel, List.map_map, Function.comp_def]

theorem optimum_le_optimum_relabel {W : Type*} (f : V → W) (φ : MaxSAT V) :
    φ.optimum ≤ (φ.relabel f).optimum :=
  optimum_le_optimum_of_forall fun τ hτ =>
    ⟨τ ∘ f, (feasible_relabel f φ τ).1 hτ, (cost_relabel f φ τ).symm.le⟩

/-- Relabelling along an injective variable map preserves the MaxSAT optimum. -/
theorem optimum_relabel {W : Type*} {f : V → W} (hf : Function.Injective f) (φ : MaxSAT V) :
    (φ.relabel f).optimum = φ.optimum := by
  classical
  refine le_antisymm ?_ (optimum_le_optimum_relabel f φ)
  refine optimum_le_optimum_of_forall fun σ hσ => ?_
  let τ : W → Bool := fun w => if h : ∃ v, f v = w then σ h.choose else false
  have hcomp : τ ∘ f = σ := funext fun v => by
    have hex : ∃ u, f u = f v := ⟨v, rfl⟩
    simpa [Function.comp_apply, τ, dite_eq_left hex] using congrArg σ (hf hex.choose_spec)
  refine ⟨τ, (feasible_relabel f φ τ).2 (hcomp ▸ hσ), ?_⟩
  rw [cost_relabel, hcomp]

private theorem cost_sublist_aux {l₁ l₂ : List (Clause V × ℕ)} (hs : l₁.Sublist l₂)
    (σ : V → Bool) :
    (l₁.map fun cw => if cw.1.eval σ then 0 else cw.2).sum ≤
      (l₂.map fun cw => if cw.1.eval σ then 0 else cw.2).sum := by
  induction hs with
  | slnil => simp
  | cons a _ ih =>
    simp only [List.map_cons, List.sum_cons]
    omega
  | cons_cons a _ ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add_left ih _

theorem cost_le_of_sublist {φ ψ : MaxSAT V} (hs : φ.soft.Sublist ψ.soft) (σ : V → Bool) :
    φ.cost σ ≤ ψ.cost σ :=
  cost_sublist_aux hs σ

/-- Adding hard clauses or additional soft clauses can only increase or leave unchanged the
optimum cost. -/
theorem optimum_le_of_sublist {φ ψ : MaxSAT V} (hh : ∀ c ∈ φ.hard, c ∈ ψ.hard)
    (hs : φ.soft.Sublist ψ.soft) : φ.optimum ≤ ψ.optimum :=
  optimum_le_optimum_of_forall fun τ hτ => by
    refine ⟨τ, (CNF.eval_eq_true_iff τ φ.hard).2 fun c hc => ?_, cost_le_of_sublist hs τ⟩
    exact (CNF.eval_eq_true_iff τ ψ.hard).1 hτ c (hh c hc)

theorem optimum_le_append_hard (φ : MaxSAT V) (h' : CNF V) :
    φ.optimum ≤ ({ hard := φ.hard ++ h', soft := φ.soft } : MaxSAT V).optimum :=
  optimum_le_of_sublist (fun _ hc => List.mem_append_left _ hc) (List.Sublist.refl _)

theorem optimum_le_append_soft (φ : MaxSAT V) (s' : List (Clause V × ℕ)) :
    φ.optimum ≤ ({ hard := φ.hard, soft := φ.soft ++ s' } : MaxSAT V).optimum :=
  optimum_le_of_sublist (fun _ hc => hc) (List.sublist_append_left φ.soft s')

end MaxSAT

/-! ### Propositional weighted partial MaxSAT and Tseitin / Plaisted–Greenbaum translations -/

namespace Proposition

/-- All atom occurrences appearing in a proposition. -/
def atoms {Atom : Type*} : Proposition Atom → List Atom
  | atom x => [x]
  | falsum => []
  | and A B | or A B | imp A B => A.atoms ++ B.atoms

theorem eval_congr {Atom : Type*} {v w : Atom → Bool} {A : Proposition Atom}
    (h : ∀ x ∈ A.atoms, v x = w x) : A.eval v = A.eval w := by
  induction A with
  | atom x => exact h x List.mem_cons_self
  | falsum => rfl
  | and A B ihA ihB =>
    simp only [eval_and_bool]
    rw [ihA fun x hx => h x (List.mem_append_left _ hx),
      ihB fun x hx => h x (List.mem_append_right _ hx)]
  | or A B ihA ihB =>
    simp only [eval_or_bool]
    rw [ihA fun x hx => h x (List.mem_append_left _ hx),
      ihB fun x hx => h x (List.mem_append_right _ hx)]
  | imp A B ihA ihB =>
    simp only [eval_imp_bool]
    rw [ihA fun x hx => h x (List.mem_append_left _ hx),
      ihB fun x hx => h x (List.mem_append_right _ hx)]

end Proposition

/-- A weighted partial MaxSAT instance over arbitrary propositions. -/
@[ext]
structure PropMaxSAT (Atom : Type*) where
  /-- Propositions that must evaluate to `true` under every feasible assignment. -/
  hard : List (Proposition Atom)
  /-- Soft propositions paired with non-negative integer weights. -/
  soft : List (Proposition Atom × ℕ)

namespace PropMaxSAT

variable {Atom : Type*}

/-- All hard and soft propositions of `ψ`. -/
def allProps (ψ : PropMaxSAT Atom) : List (Proposition Atom) :=
  ψ.hard ++ ψ.soft.map Prod.fst

/-- Sum of syntactic sizes of all hard and soft propositions of `ψ`. -/
def totalSize (ψ : PropMaxSAT Atom) : ℕ :=
  (ψ.allProps.map Proposition.size).sum

/-- All atom occurrences appearing in `ψ`. -/
def atoms (ψ : PropMaxSAT Atom) : List Atom :=
  ψ.allProps.flatMap Proposition.atoms

/-- An atom valuation is feasible when every hard proposition holds. -/
def feasible (ψ : PropMaxSAT Atom) (v : Atom → Bool) : Prop :=
  ∀ A ∈ ψ.hard, A.eval v = true

/-- Total weight of soft propositions falsified by `v`. -/
def cost (ψ : PropMaxSAT Atom) (v : Atom → Bool) : ℕ :=
  (ψ.soft.map fun Aw => if Aw.1.eval v then 0 else Aw.2).sum

/-- Total weight of all soft propositions in `ψ`. -/
def totalWeight (ψ : PropMaxSAT Atom) : ℕ :=
  (ψ.soft.map Prod.snd).sum

/-- Total weight of soft propositions satisfied by `v`. -/
def satisfiedWeight (ψ : PropMaxSAT Atom) (v : Atom → Bool) : ℕ :=
  (ψ.soft.map fun Aw => if Aw.1.eval v then Aw.2 else 0).sum

theorem feasible_congr {ψ : PropMaxSAT Atom} {v w : Atom → Bool}
    (h : ∀ x ∈ ψ.atoms, v x = w x) : ψ.feasible v ↔ ψ.feasible w := by
  have hev : ∀ A ∈ ψ.hard, A.eval v = A.eval w := fun A hA =>
    Proposition.eval_congr fun x hx =>
      h x (List.mem_flatMap.2 ⟨A, List.mem_append_left _ hA, hx⟩)
  exact ⟨fun hv A hA => (hev A hA).symm.trans (hv A hA),
    fun hw A hA => (hev A hA).trans (hw A hA)⟩

theorem cost_congr {ψ : PropMaxSAT Atom} {v w : Atom → Bool}
    (h : ∀ x ∈ ψ.atoms, v x = w x) : ψ.cost v = ψ.cost w := by
  unfold cost
  congr 1
  refine List.map_congr_left fun Aw hAw => ?_
  have hev : Aw.1.eval v = Aw.1.eval w :=
    Proposition.eval_congr fun x hx =>
      h x (List.mem_flatMap.2 ⟨Aw.1, List.mem_append_right _ (List.mem_map.2 ⟨Aw, hAw, rfl⟩), hx⟩)
  rw [hev]

/-- Minimum cost among feasible atom valuations of `ψ`, or `⊤` when `ψ.hard` is unsatisfiable. -/
noncomputable def optimum (ψ : PropMaxSAT Atom) : WithTop ℕ :=
  open Classical in
  if h : ∃ v : Atom → Bool, ψ.feasible v then
    ((Nat.find (⟨ψ.cost h.choose, h.choose, h.choose_spec, rfl⟩ :
      ∃ k : ℕ, ∃ v : Atom → Bool, ψ.feasible v ∧ ψ.cost v = k) : ℕ) : WithTop ℕ)
  else ⊤

theorem optimum_eq_top_iff (ψ : PropMaxSAT Atom) : ψ.optimum = ⊤ ↔ ¬ ∃ v, ψ.feasible v := by
  classical
  unfold optimum
  split_ifs with h
  · simpa [WithTop.coe_ne_top] using h
  · exact iff_of_true rfl h

theorem optimum_ne_top_iff (ψ : PropMaxSAT Atom) : ψ.optimum ≠ ⊤ ↔ ∃ v, ψ.feasible v := by
  rw [ne_eq, optimum_eq_top_iff, not_not]

theorem exists_feasible_cost_eq_optimum {ψ : PropMaxSAT Atom} (h : ∃ v, ψ.feasible v) :
    ∃ v : Atom → Bool, ψ.feasible v ∧ (ψ.cost v : WithTop ℕ) = ψ.optimum := by
  classical
  unfold optimum
  rw [dite_eq_left h]
  obtain ⟨v, hv, hcost⟩ :=
    Nat.find_spec (⟨ψ.cost h.choose, h.choose, h.choose_spec, rfl⟩ :
      ∃ k : ℕ, ∃ v : Atom → Bool, ψ.feasible v ∧ ψ.cost v = k)
  exact ⟨v, hv, congrArg ((↑) : ℕ → WithTop ℕ) hcost⟩

theorem optimum_le_cost {ψ : PropMaxSAT Atom} {v : Atom → Bool} (hv : ψ.feasible v) :
    ψ.optimum ≤ (ψ.cost v : WithTop ℕ) := by
  classical
  have h : ∃ v : Atom → Bool, ψ.feasible v := ⟨v, hv⟩
  unfold optimum
  rw [dite_eq_left h]
  exact WithTop.coe_le_coe.2 (Nat.find_min' _ ⟨v, hv, rfl⟩)

theorem le_optimum_iff {ψ : PropMaxSAT Atom} {k : ℕ} :
    (k : WithTop ℕ) ≤ ψ.optimum ↔ ∀ v : Atom → Bool, ψ.feasible v → k ≤ ψ.cost v := by
  refine ⟨fun hk v hv => WithTop.coe_le_coe.1 (hk.trans (optimum_le_cost hv)), fun hk => ?_⟩
  by_cases hsat : ∃ v, ψ.feasible v
  · obtain ⟨v, hv, hopt⟩ := exists_feasible_cost_eq_optimum hsat
    rw [← hopt]
    exact WithTop.coe_le_coe.2 (hk v hv)
  · rw [ψ.optimum_eq_top_iff.2 hsat]
    exact le_top

/-- Computable branch-and-enumerate optimum over a list of atoms. -/
def optimumOn [DecidableEq Atom] (ψ : PropMaxSAT Atom) :
    List Atom → (Atom → Bool) → WithTop ℕ
  | [], v => if ψ.hard.all (fun A => A.eval v) then (ψ.cost v : WithTop ℕ) else ⊤
  | x :: xs, v =>
      min (ψ.optimumOn xs (fun y => if y = x then true else v y))
          (ψ.optimumOn xs (fun y => if y = x then false else v y))

private theorem optimumOn_le_of_agree [DecidableEq Atom] (ψ : PropMaxSAT Atom) (xs : List Atom)
    (v w : Atom → Bool) (hw : ψ.feasible w) (hout : ∀ y, y ∉ xs → w y = v y) :
    ψ.optimumOn xs v ≤ (ψ.cost w : WithTop ℕ) := by
  induction xs generalizing v with
  | nil =>
    have heq : w = v := funext fun y => hout y List.not_mem_nil
    have hall : ψ.hard.all (fun A => A.eval v) = true := List.all_eq_true.2 (heq ▸ hw)
    simp only [optimumOn, heq, hall]
    exact le_rfl
  | cons x xs ih =>
    simp only [optimumOn]
    have hnot : ∀ y, y ∉ xs → y ≠ x → w y = v y := fun y hy hne =>
      hout y fun hm => by
        rcases List.mem_cons.1 hm with rfl | hm
        · exact hne rfl
        · exact hy hm
    cases hx : w x
    · refine min_le_of_right_le (ih (fun y => if y = x then false else v y) fun y hy => ?_)
      by_cases hyeq : y = x
      · simp [hyeq, hx]
      · simp [hyeq, hnot y hy hyeq]
    · refine min_le_of_left_le (ih (fun y => if y = x then true else v y) fun y hy => ?_)
      by_cases hyeq : y = x
      · simp [hyeq, hx]
      · simp [hyeq, hnot y hy hyeq]

private theorem optimumOn_witness_or_top [DecidableEq Atom] (ψ : PropMaxSAT Atom) (xs : List Atom)
    (v : Atom → Bool) :
    ψ.optimumOn xs v = ⊤ ∨
      ∃ w : Atom → Bool, (∀ y, y ∉ xs → w y = v y) ∧
        ψ.feasible w ∧ ψ.optimumOn xs v = (ψ.cost w : WithTop ℕ) := by
  induction xs generalizing v with
  | nil =>
    simp only [optimumOn]
    split_ifs with h
    · exact .inr ⟨v, fun _ _ => rfl, List.all_eq_true.1 h, rfl⟩
    · exact .inl rfl
  | cons x xs ih =>
    simp only [optimumOn]
    set vt : Atom → Bool := fun y => if y = x then true else v y
    set vf : Atom → Bool := fun y => if y = x then false else v y
    rcases le_total (ψ.optimumOn xs vt) (ψ.optimumOn xs vf) with hle | hle
    · rw [min_eq_left hle]
      rcases ih vt with ht | ⟨w, hout, hfeas, hcost⟩
      · exact .inl ht
      · refine .inr ⟨w, fun y hy => ?_, hfeas, hcost⟩
        have hnotxs : y ∉ xs := fun hm => hy (List.mem_cons_of_mem x hm)
        have hne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self)
        simpa [vt, hne] using hout y hnotxs
    · rw [min_eq_right hle]
      rcases ih vf with hf | ⟨w, hout, hfeas, hcost⟩
      · exact .inl hf
      · refine .inr ⟨w, fun y hy => ?_, hfeas, hcost⟩
        have hnotxs : y ∉ xs := fun hm => hy (List.mem_cons_of_mem x hm)
        have hne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self)
        simpa [vf, hne] using hout y hnotxs

theorem optimumOn_eq_optimum [DecidableEq Atom] (ψ : PropMaxSAT Atom) (xs : List Atom)
    (hatoms : ∀ x ∈ ψ.atoms, x ∈ xs) (v : Atom → Bool) :
    ψ.optimumOn xs v = ψ.optimum := by
  rcases optimumOn_witness_or_top ψ xs v with htop | ⟨w, _, hfeas, hcost⟩
  · have hunsat : ¬ ∃ u, ψ.feasible u := by
      rintro ⟨u, hu⟩
      let u' : Atom → Bool := fun y => if y ∈ xs then u y else v y
      have hagree : ∀ y ∈ ψ.atoms, u' y = u y := fun y hy => by simp [u', hatoms y hy]
      have hle := optimumOn_le_of_agree ψ xs v u' ((feasible_congr hagree).2 hu)
        (fun y hy => by simp [u', hy])
      rw [htop, top_le_iff] at hle
      exact absurd hle (by simp)
    rw [htop, ψ.optimum_eq_top_iff.2 hunsat]
  · refine le_antisymm ?_ (hcost ▸ optimum_le_cost hfeas)
    by_cases hsat : ∃ u, ψ.feasible u
    · obtain ⟨u, hu, hopt⟩ := exists_feasible_cost_eq_optimum hsat
      let u' : Atom → Bool := fun y => if y ∈ xs then u y else v y
      have hagree : ∀ y ∈ ψ.atoms, u' y = u y := fun y hy => by simp [u', hatoms y hy]
      have hle := optimumOn_le_of_agree ψ xs v u' ((feasible_congr hagree).2 hu)
        (fun y hy => by simp [u', hy])
      rwa [cost_congr hagree, hopt] at hle
    · rw [ψ.optimum_eq_top_iff.2 hsat]
      exact le_top

/-- Computable optimum for propositional MaxSAT instances over atoms with decidable equality. -/
def computeOptimum [DecidableEq Atom] (ψ : PropMaxSAT Atom) : WithTop ℕ :=
  ψ.optimumOn (MaxSAT.dedupVars ψ.atoms) (fun _ => false)

theorem computeOptimum_eq_optimum [DecidableEq Atom] (ψ : PropMaxSAT Atom) :
    ψ.computeOptimum = ψ.optimum :=
  optimumOn_eq_optimum ψ (MaxSAT.dedupVars ψ.atoms)
    (fun _ hx => MaxSAT.mem_dedupVars.2 hx) _

/-! #### Tseitin translation -/

/-- The Tseitin translation of `ψ` into a clausal weighted partial MaxSAT instance: hard
definitional clauses for every hard and soft proposition, unit hard clauses for `ψ.hard`, and
unit soft clauses for `ψ.soft` preserving weights. -/
def toTseitin (ψ : PropMaxSAT Atom) : MaxSAT (Atom ⊕ Proposition Atom) where
  hard := ψ.allProps.flatMap Proposition.tseitinDefs ++
    ψ.hard.map fun A => [(A.tseitinVar, true)]
  soft := ψ.soft.map fun Aw => ([(Aw.1.tseitinVar, true)], Aw.2)

theorem feasible_toTseitin_tseitinExtend {ψ : PropMaxSAT Atom} {v : Atom → Bool}
    (hv : ψ.feasible v) : ψ.toTseitin.feasible (Proposition.tseitinExtend v) := by
  simp only [MaxSAT.feasible, toTseitin, CNF.eval_append, Bool.and_eq_true,
    Proposition.eval_tseitinDefs_flatMap_tseitinExtend, true_and, CNF.eval_eq_true_iff,
    List.mem_map]
  rintro c ⟨A, hA, rfl⟩
  simpa [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, Proposition.tseitinExtend_tseitinVar]
    using hv A hA

theorem cost_toTseitin_tseitinExtend (ψ : PropMaxSAT Atom) (v : Atom → Bool) :
    ψ.toTseitin.cost (Proposition.tseitinExtend v) = ψ.cost v := by
  unfold MaxSAT.cost cost toTseitin
  simp [List.map_map, Function.comp_def, Clause.eval_cons, Literal.eval_mk, Clause.eval_nil,
    Proposition.tseitinExtend_tseitinVar]

theorem feasible_of_feasible_toTseitin {ψ : PropMaxSAT Atom}
    {σ : Atom ⊕ Proposition Atom → Bool} (hσ : ψ.toTseitin.feasible σ) :
    ψ.feasible (σ ∘ Sum.inl) := by
  simp only [MaxSAT.feasible, toTseitin, CNF.eval_append, Bool.and_eq_true] at hσ
  intro A hA
  have hdefs : A.tseitinDefs.eval σ = true :=
    (Proposition.eval_tseitinDefs_flatMap_iff σ ψ.allProps).1 hσ.1 A
      (List.mem_append_left _ hA)
  have hunit : Clause.eval σ [(A.tseitinVar, true)] = true :=
    (CNF.eval_eq_true_iff σ _).1 hσ.2 _ (List.mem_map.2 ⟨A, hA, rfl⟩)
  simp only [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, Bool.or_false, beq_iff_eq]
    at hunit
  exact (Proposition.eval_tseitinVar_of_eval_tseitinDefs hdefs).symm.trans hunit

theorem cost_toTseitin_eq {ψ : PropMaxSAT Atom} {σ : Atom ⊕ Proposition Atom → Bool}
    (hσ : ψ.toTseitin.feasible σ) : ψ.toTseitin.cost σ = ψ.cost (σ ∘ Sum.inl) := by
  simp only [MaxSAT.feasible, toTseitin, CNF.eval_append, Bool.and_eq_true] at hσ
  unfold MaxSAT.cost cost toTseitin
  simp only [List.map_map, Function.comp_def]
  congr 1
  refine List.map_congr_left fun Aw hAw => ?_
  have hdefs : Aw.1.tseitinDefs.eval σ = true :=
    (Proposition.eval_tseitinDefs_flatMap_iff σ ψ.allProps).1 hσ.1 Aw.1
      (List.mem_append_right _ (List.mem_map.2 ⟨Aw, hAw, rfl⟩))
  have hvar : σ Aw.1.tseitinVar = Aw.1.eval (σ ∘ Sum.inl) :=
    Proposition.eval_tseitinVar_of_eval_tseitinDefs hdefs
  simp [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, hvar, Function.comp_def]

/-- Under a feasible assignment for `ψ.toTseitin`, every variable appearing in `ψ.toTseitin`
carries the value assigned by `Proposition.tseitinExtend` to its atom restriction. -/
theorem eq_tseitinExtend_of_feasible_toTseitin {ψ : PropMaxSAT Atom}
    {σ : Atom ⊕ Proposition Atom → Bool} (hσ : ψ.toTseitin.feasible σ)
    {y : Atom ⊕ Proposition Atom} (hy : y ∈ ψ.toTseitin.vars) :
    σ y = Proposition.tseitinExtend (σ ∘ Sum.inl) y := by
  simp only [MaxSAT.feasible, toTseitin, CNF.eval_append, Bool.and_eq_true] at hσ
  simp only [MaxSAT.vars, MaxSAT.softClauses, toTseitin, List.mem_append, List.map_map] at hy
  rcases hy with hyhard | hysoft
  · obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 hyhard
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with hcdefs | ⟨A, hA, rfl⟩
    · exact Proposition.eq_tseitinExtend_of_eval_tseitinDefs_flatMap hσ.1
        (CNF.mem_vars.2 ⟨c, hcdefs, b, hb⟩)
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb
      rcases hb with ⟨rfl, -⟩
      have hdefs := (Proposition.eval_tseitinDefs_flatMap_iff σ ψ.allProps).1 hσ.1 A
        (List.mem_append_left _ hA)
      exact Proposition.eq_tseitinExtend_of_eval_tseitinDefs hdefs (.inl rfl)
  · obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 hysoft
    simp only [List.mem_map, Function.comp_def] at hc
    obtain ⟨Aw, hAw, rfl⟩ := hc
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb
    rcases hb with ⟨rfl, -⟩
    have hdefs := (Proposition.eval_tseitinDefs_flatMap_iff σ ψ.allProps).1 hσ.1 Aw.1
      (List.mem_append_right _ (List.mem_map.2 ⟨Aw, hAw, rfl⟩))
    exact Proposition.eq_tseitinExtend_of_eval_tseitinDefs hdefs (.inl rfl)

/-- Feasible assignments for `ψ.toTseitin` are uniquely determined on the variables of
`ψ.toTseitin` by their restriction to the atoms. -/
theorem eq_of_feasible_toTseitin {ψ : PropMaxSAT Atom}
    {σ τ : Atom ⊕ Proposition Atom → Bool}
    (hσ : ψ.toTseitin.feasible σ) (hτ : ψ.toTseitin.feasible τ)
    (hatoms : σ ∘ Sum.inl = τ ∘ Sum.inl) {y : Atom ⊕ Proposition Atom}
    (hy : y ∈ ψ.toTseitin.vars) : σ y = τ y := by
  rw [eq_tseitinExtend_of_feasible_toTseitin hσ hy,
    eq_tseitinExtend_of_feasible_toTseitin hτ hy, hatoms]

/-- **The Tseitin translation preserves the MaxSAT optimum.** -/
theorem optimum_toTseitin (ψ : PropMaxSAT Atom) : ψ.toTseitin.optimum = ψ.optimum := by
  refine le_antisymm ?_ ?_
  · by_cases hsat : ∃ v, ψ.feasible v
    · obtain ⟨v, hv, hopt⟩ := exists_feasible_cost_eq_optimum hsat
      rw [← hopt, ← cost_toTseitin_tseitinExtend ψ v]
      exact MaxSAT.optimum_le_cost (feasible_toTseitin_tseitinExtend hv)
    · rw [ψ.optimum_eq_top_iff.2 hsat]
      exact le_top
  · by_cases hsat : ψ.toTseitin.hard.Satisfiable
    · obtain ⟨σ, hσ, hopt⟩ := MaxSAT.exists_feasible_cost_eq_optimum hsat
      rw [← hopt, cost_toTseitin_eq hσ]
      exact optimum_le_cost (feasible_of_feasible_toTseitin hσ)
    · rw [ψ.toTseitin.optimum_eq_top_iff.2 hsat]
      exact le_top

theorem length_hard_toTseitin_le (ψ : PropMaxSAT Atom) :
    ψ.toTseitin.hard.length ≤ 3 * ψ.totalSize + ψ.hard.length := by
  simp only [toTseitin, totalSize, List.length_append, List.length_map]
  exact Nat.add_le_add_right (Proposition.length_tseitinDefs_flatMap_le ψ.allProps) _

@[simp]
theorem length_soft_toTseitin (ψ : PropMaxSAT Atom) : ψ.toTseitin.soft.length = ψ.soft.length := by
  simp [toTseitin]

theorem length_le_three_of_mem_toTseitin_hard {ψ : PropMaxSAT Atom}
    {c : Clause (Atom ⊕ Proposition Atom)} (hc : c ∈ ψ.toTseitin.hard) : c.length ≤ 3 := by
  simp only [toTseitin, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with ⟨A, -, hcA⟩ | ⟨A, -, rfl⟩
  · exact Proposition.length_le_three_of_mem_tseitinDefs hcA
  · simp

theorem length_le_three_of_mem_toTseitin_soft {ψ : PropMaxSAT Atom}
    {cw : Clause (Atom ⊕ Proposition Atom) × ℕ} (hcw : cw ∈ ψ.toTseitin.soft) :
    cw.1.length ≤ 3 := by
  simp only [toTseitin, List.mem_map] at hcw
  obtain ⟨Aw, -, rfl⟩ := hcw
  simp

/-! #### Plaisted–Greenbaum translation -/

/-- The positive-polarity Plaisted–Greenbaum translation of `ψ` into a clausal weighted partial
MaxSAT instance. -/
def toPlaistedGreenbaum (ψ : PropMaxSAT Atom) : MaxSAT (Atom ⊕ Proposition Atom) where
  hard := ψ.allProps.flatMap (Proposition.plaistedGreenbaumDefs true) ++
    ψ.hard.map fun A => [(A.tseitinVar, true)]
  soft := ψ.soft.map fun Aw => ([(Aw.1.tseitinVar, true)], Aw.2)

theorem feasible_toPlaistedGreenbaum_tseitinExtend {ψ : PropMaxSAT Atom} {v : Atom → Bool}
    (hv : ψ.feasible v) : ψ.toPlaistedGreenbaum.feasible (Proposition.tseitinExtend v) := by
  simp only [MaxSAT.feasible, toPlaistedGreenbaum, CNF.eval_append, Bool.and_eq_true,
    Proposition.eval_plaistedGreenbaumDefs_flatMap_tseitinExtend, true_and, CNF.eval_eq_true_iff,
    List.mem_map]
  rintro c ⟨A, hA, rfl⟩
  simpa [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, Proposition.tseitinExtend_tseitinVar]
    using hv A hA

theorem cost_toPlaistedGreenbaum_tseitinExtend (ψ : PropMaxSAT Atom) (v : Atom → Bool) :
    ψ.toPlaistedGreenbaum.cost (Proposition.tseitinExtend v) = ψ.cost v := by
  unfold MaxSAT.cost cost toPlaistedGreenbaum
  simp [List.map_map, Function.comp_def, Clause.eval_cons, Literal.eval_mk, Clause.eval_nil,
    Proposition.tseitinExtend_tseitinVar]

theorem feasible_of_feasible_toPlaistedGreenbaum {ψ : PropMaxSAT Atom}
    {σ : Atom ⊕ Proposition Atom → Bool} (hσ : ψ.toPlaistedGreenbaum.feasible σ) :
    ψ.feasible (σ ∘ Sum.inl) := by
  simp only [MaxSAT.feasible, toPlaistedGreenbaum, CNF.eval_append, Bool.and_eq_true] at hσ
  intro A hA
  have hdefs : (A.plaistedGreenbaumDefs true).eval σ = true :=
    (Proposition.eval_plaistedGreenbaumDefs_flatMap_iff σ ψ.allProps).1 hσ.1 A
      (List.mem_append_left _ hA)
  have hunit : Clause.eval σ [(A.tseitinVar, true)] = true :=
    (CNF.eval_eq_true_iff σ _).1 hσ.2 _ (List.mem_map.2 ⟨A, hA, rfl⟩)
  simp only [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, Bool.or_false, beq_iff_eq]
    at hunit
  exact Proposition.eval_eq_of_eval_plaistedGreenbaumDefs hdefs hunit

/-- Under a feasible assignment for `ψ.toPlaistedGreenbaum`, the cost of its atom restriction
never exceeds the cost of the translated assignment. -/
theorem cost_le_cost_toPlaistedGreenbaum {ψ : PropMaxSAT Atom}
    {σ : Atom ⊕ Proposition Atom → Bool} (hσ : ψ.toPlaistedGreenbaum.feasible σ) :
    ψ.cost (σ ∘ Sum.inl) ≤ ψ.toPlaistedGreenbaum.cost σ := by
  simp only [MaxSAT.feasible, toPlaistedGreenbaum, CNF.eval_append, Bool.and_eq_true] at hσ
  unfold cost MaxSAT.cost toPlaistedGreenbaum
  simp only [List.map_map, Function.comp_def]
  refine list_sum_map_le_sum_map ψ.soft _ _ fun Aw hAw => ?_
  have hdefs : (Aw.1.plaistedGreenbaumDefs true).eval σ = true :=
    (Proposition.eval_plaistedGreenbaumDefs_flatMap_iff σ ψ.allProps).1 hσ.1 Aw.1
      (List.mem_append_right _ (List.mem_map.2 ⟨Aw, hAw, rfl⟩))
  by_cases hvar : σ Aw.1.tseitinVar = true
  · have hprop : Aw.1.eval (fun x => σ (Sum.inl x)) = true :=
      Proposition.eval_eq_of_eval_plaistedGreenbaumDefs hdefs hvar
    have hcl : Clause.eval σ [(Aw.1.tseitinVar, true)] = true := by
      simp [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, hvar]
    simp [hprop, hcl]
  · have hfal : Clause.eval σ [(Aw.1.tseitinVar, true)] = false := by
      simp [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, hvar]
    by_cases hprop : Aw.1.eval (fun x => σ (Sum.inl x)) = true <;> simp [hfal, hprop]

/-- **The Plaisted–Greenbaum translation preserves the MaxSAT optimum.** -/
theorem optimum_toPlaistedGreenbaum (ψ : PropMaxSAT Atom) :
    ψ.toPlaistedGreenbaum.optimum = ψ.optimum := by
  refine le_antisymm ?_ ?_
  · by_cases hsat : ∃ v, ψ.feasible v
    · obtain ⟨v, hv, hopt⟩ := exists_feasible_cost_eq_optimum hsat
      rw [← hopt, ← cost_toPlaistedGreenbaum_tseitinExtend ψ v]
      exact MaxSAT.optimum_le_cost (feasible_toPlaistedGreenbaum_tseitinExtend hv)
    · rw [ψ.optimum_eq_top_iff.2 hsat]
      exact le_top
  · by_cases hsat : ψ.toPlaistedGreenbaum.hard.Satisfiable
    · obtain ⟨σ, hσ, hopt⟩ := MaxSAT.exists_feasible_cost_eq_optimum hsat
      have hle : ψ.optimum ≤ (ψ.cost (σ ∘ Sum.inl) : WithTop ℕ) :=
        optimum_le_cost (feasible_of_feasible_toPlaistedGreenbaum hσ)
      exact hle.trans ((WithTop.coe_le_coe.2 (cost_le_cost_toPlaistedGreenbaum hσ)).trans_eq hopt)
    · rw [ψ.toPlaistedGreenbaum.optimum_eq_top_iff.2 hsat]
      exact le_top

/-- Unlike `PropMaxSAT.toTseitin`, feasible assignments for `PropMaxSAT.toPlaistedGreenbaum` are
not uniquely determined by their restriction to atoms even on all variables of the translation. -/
theorem not_forall_eq_of_feasible_toPlaistedGreenbaum [Nonempty Atom] :
    ¬ ∀ (ψ : PropMaxSAT Atom) (σ τ : Atom ⊕ Proposition Atom → Bool),
      ψ.toPlaistedGreenbaum.feasible σ → ψ.toPlaistedGreenbaum.feasible τ →
        σ ∘ Sum.inl = τ ∘ Sum.inl → ∀ y ∈ ψ.toPlaistedGreenbaum.vars, σ y = τ y := by
  intro h
  have hsingle : ∀ (A : Proposition Atom) (σ τ : Atom ⊕ Proposition Atom → Bool),
      A.plaistedGreenbaumCNF.eval σ = true → A.plaistedGreenbaumCNF.eval τ = true →
        σ ∘ Sum.inl = τ ∘ Sum.inl → ∀ y ∈ A.plaistedGreenbaumCNF.vars, σ y = τ y := by
    intro A σ τ hσ hτ hatoms y hy
    simp only [Proposition.plaistedGreenbaumCNF, CNF.eval_cons, Clause.eval_cons, Literal.eval_mk,
      Clause.eval_nil, Bool.or_false, beq_iff_eq, Bool.and_eq_true] at hσ hτ
    have hσf : ({ hard := [A], soft := [] } : PropMaxSAT Atom).toPlaistedGreenbaum.feasible σ := by
      simp [MaxSAT.feasible, toPlaistedGreenbaum, allProps, hσ.1, hσ.2]
    have hτf : ({ hard := [A], soft := [] } : PropMaxSAT Atom).toPlaistedGreenbaum.feasible τ := by
      simp [MaxSAT.feasible, toPlaistedGreenbaum, allProps, hτ.1, hτ.2]
    have hy' : y ∈ ({ hard := [A], soft := [] } : PropMaxSAT Atom).toPlaistedGreenbaum.vars := by
      obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 hy
      refine List.mem_append_left _ (CNF.mem_vars.2 ⟨c, ?_, b, hb⟩)
      rcases List.mem_cons.1 hc with rfl | hc
      · exact List.mem_append_right _ (List.mem_map.2 ⟨A, List.mem_cons_self, rfl⟩)
      · exact List.mem_append_left _
          (List.mem_flatMap.2 ⟨A, List.mem_append_left _ List.mem_cons_self, hc⟩)
    exact h ⟨[A], []⟩ σ τ hσf hτf hatoms y hy'
  exact Proposition.not_forall_eq_of_eval_plaistedGreenbaumCNF hsingle

theorem length_hard_toPlaistedGreenbaum_le (ψ : PropMaxSAT Atom) :
    ψ.toPlaistedGreenbaum.hard.length ≤ 2 * ψ.totalSize + ψ.hard.length := by
  simp only [toPlaistedGreenbaum, totalSize, List.length_append, List.length_map]
  exact Nat.add_le_add_right (Proposition.length_plaistedGreenbaumDefs_flatMap_le ψ.allProps) _

@[simp]
theorem length_soft_toPlaistedGreenbaum (ψ : PropMaxSAT Atom) :
    ψ.toPlaistedGreenbaum.soft.length = ψ.soft.length := by
  simp [toPlaistedGreenbaum]

theorem length_le_three_of_mem_toPlaistedGreenbaum_hard {ψ : PropMaxSAT Atom}
    {c : Clause (Atom ⊕ Proposition Atom)} (hc : c ∈ ψ.toPlaistedGreenbaum.hard) :
    c.length ≤ 3 := by
  simp only [toPlaistedGreenbaum, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with ⟨A, -, hcA⟩ | ⟨A, -, rfl⟩
  · exact Proposition.length_le_three_of_mem_plaistedGreenbaumDefs hcA
  · simp

theorem length_le_three_of_mem_toPlaistedGreenbaum_soft {ψ : PropMaxSAT Atom}
    {cw : Clause (Atom ⊕ Proposition Atom) × ℕ} (hcw : cw ∈ ψ.toPlaistedGreenbaum.soft) :
    cw.1.length ≤ 3 := by
  simp only [toPlaistedGreenbaum, List.mem_map] at hcw
  obtain ⟨Aw, -, rfl⟩ := hcw
  simp

end PropMaxSAT

end Cslib.Logic.PL
