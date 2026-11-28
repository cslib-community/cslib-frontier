/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Dimacs
public import CslibFrontier.Logics.Propositional.MaxSAT
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Completeness
import CslibFrontier.Logics.Propositional.CNF.Eval
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Weighted partial MaxSAT as pseudo-Boolean optimization

A weighted partial MaxSAT instance `φ : MaxSAT ℕ` (`Cslib.Logic.PL.MaxSAT`) is encoded as a
pseudo-Boolean formula `φ.toPBConstrs` with an objective `φ.toObjective` to minimize, by the
relaxation-variable encoding [Bacchus, Järvisalo and Martins][BacchusJarvisaloMartins2021]:

* each hard clause `C` becomes the constraint `Clause.toPB C`;
* the soft clause `Cᵢ` of weight `wᵢ` at index `i` gets the relaxation variable
  `bᵢ = φ.relaxBase + i`, above every variable of the instance, and becomes the constraint
  `Clause.toPB (Cᵢ ++ [bᵢ])` and the objective term `wᵢ bᵢ`;
* a soft unit clause `[ℓ]` needs no relaxation variable: it becomes no constraint and the
  objective term `wᵢ ¬ℓ`, written `-wᵢ x + wᵢ` for `ℓ = x` and `wᵢ x` for `ℓ = ¬x`.

**Correctness.** A feasible assignment `σ` extends, by `bᵢ := ¬Cᵢ(σ)`, to a solution
`φ.extend σ` of the encoding whose objective value is the cost of `σ`
(`Cslib.Logic.PL.MaxSAT.holds_toPBConstrs_extend`, `Cslib.Logic.PL.MaxSAT.eval_extend`).
Conversely every solution `τ` of the encoding is feasible, with cost at most its objective
value (`Cslib.Logic.PL.MaxSAT.feasible_of_holds_toPBConstrs`,
`Cslib.Logic.PL.MaxSAT.cost_le_eval_of_holds_toPBConstrs`). So `v` is the least objective
value of a solution iff it is the least cost of a feasible assignment
(`Cslib.Logic.PL.MaxSAT.isLeast_eval_iff`), and the encoding has a solution iff the hard clauses
are satisfiable (`Cslib.Logic.PL.MaxSAT.exists_holds_toPBConstrs_iff`). The encoding has one
constraint per hard clause and per soft clause that is not a unit
(`Cslib.Logic.PL.MaxSAT.length_toPBConstrs`), and its only variables outside the instance are
the relaxation variables of those soft clauses
(`Cslib.Logic.PL.MaxSAT.mem_vars_toPBConstrs`, `Cslib.Logic.PL.MaxSAT.mem_lin_toObjective`).

**Certified optima.** Through the encoding, the soundness of the VeriPB kernel checker
`Cslib.Logic.PL.VeriPB.checkRed` for `BOUNDS` certifies bounds on the MaxSAT optimum: an accepted
`conclusion BOUNDS lb : q ub` bounds every feasible cost below by `lb` and gives a feasible
assignment of cost at most `ub` (`Cslib.Logic.PL.MaxSAT.le_cost_of_checkRed`,
`Cslib.Logic.PL.MaxSAT.exists_cost_le_of_checkRed`), and an accepted `BOUNDS INF` shows the hard
clauses unsatisfiable (`Cslib.Logic.PL.MaxSAT.not_satisfiable_of_checkRed_bounds`). Conversely,
by the completeness of the checker, `v` is the optimum iff some proof of `BOUNDS v : q v` is
accepted (`Cslib.Logic.PL.MaxSAT.isLeast_cost_iff_exists_checkRed_bounds`), every instance with
satisfiable hard clauses has such a proof (`Cslib.Logic.PL.MaxSAT.exists_checkRed_bounds`), and
the hard clauses are unsatisfiable iff some proof of `BOUNDS INF` is accepted
(`Cslib.Logic.PL.MaxSAT.not_satisfiable_iff_exists_checkRed_boundsInf`).

The instances are over the variables `ℕ`, as the checker's are.

## Main definitions

* `Cslib.Logic.PL.MaxSAT.toPBConstrs`, `Cslib.Logic.PL.MaxSAT.toObjective`: the encoding.
* `Cslib.Logic.PL.MaxSAT.relaxBase`: the first relaxation variable.
* `Cslib.Logic.PL.MaxSAT.extend`: an assignment extended to the relaxation variables.

## References

* [F. Bacchus, M. Järvisalo, R. Martins, *Maximum Satisfiability*][BacchusJarvisaloMartins2021]
* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]: the proof system for
  optimisation that the checker `Cslib.Logic.PL.VeriPB.checkRed` implements, with logged
  solutions and objective-improving constraints, through which the `BOUNDS` results above
  certify optima.
-/

public section

namespace Cslib.Logic.PL.MaxSAT

open VeriPB PBConstr

/-! ### The encoding -/

/-- The literal of a unit clause, and `none` for every other clause. -/
@[expose] def unitLit? : Clause ℕ → Option (Literal ℕ)
  | [l] => some l
  | _ => none

/-- The first relaxation variable: the variables of the instance are below it. -/
@[expose] def relaxBase (φ : MaxSAT ℕ) : ℕ := (φ.hard ++ φ.soft.map Prod.fst).dimacsVars

/-- The constraint of the soft clause `cw` at index `i`, with the relaxation variable `b + i`:
none for a unit clause, and `Clause.toPB (cw.1 ++ [b + i])` otherwise. -/
@[expose] def softConstr? (b : ℕ) (cw : Clause ℕ × ℕ) (i : ℕ) : Option PBConstr :=
  match unitLit? cw.1 with
  | some _ => none
  | none => some (Clause.toPB (cw.1 ++ [(b + i, true)]))

/-- The objective term and constant of the soft clause `cw` of weight `w` at index `i`: the term
`w (b + i)` of its relaxation variable, or for a unit clause `[ℓ]` the value `w ¬ℓ`, that is
`-w x + w` for `ℓ = x` and `w x` for `ℓ = ¬x`. -/
@[expose] def softTerm (b : ℕ) (cw : Clause ℕ × ℕ) (i : ℕ) : (ℕ × ℤ) × ℤ :=
  match unitLit? cw.1 with
  | some (v, true) => ((v, -(cw.2 : ℤ)), cw.2)
  | some (v, false) => ((v, cw.2), 0)
  | none => ((b + i, cw.2), 0)

/-- **The constraints of the encoding**: the hard clauses, and each soft clause that is not a
unit with its relaxation variable. -/
@[expose] def toPBConstrs (φ : MaxSAT ℕ) : List PBConstr :=
  φ.hard.map Clause.toPB ++ φ.soft.zipIdx.filterMap fun p => softConstr? φ.relaxBase p.1 p.2

/-- **The objective of the encoding**: the total weight of the relaxation variables and of the
negated literals of the soft unit clauses. -/
@[expose] def toObjective (φ : MaxSAT ℕ) : Objective :=
  ⟨φ.soft.zipIdx.map fun p => (softTerm φ.relaxBase p.1 p.2).1,
    (φ.soft.zipIdx.map fun p => (softTerm φ.relaxBase p.1 p.2).2).sum⟩

/-- The assignment `σ` extended to the relaxation variables: `relaxBase + i` is true iff `σ`
falsifies the soft clause at index `i`. -/
@[expose] def extend (φ : MaxSAT ℕ) (σ : ℕ → Bool) (v : ℕ) : Bool :=
  if v < φ.relaxBase then σ v else !((φ.soft[v - φ.relaxBase]?).all fun cw => cw.1.eval σ)

/-! ### Basic facts -/

theorem unitLit?_eq_some {c : Clause ℕ} {l : Literal ℕ} : unitLit? c = some l ↔ c = [l] := by
  match c with
  | [] => simp [unitLit?]
  | [l'] => simp [unitLit?, eq_comm]
  | _ :: _ :: _ => simp [unitLit?]

variable {φ : MaxSAT ℕ}

private theorem lt_relaxBase {c : Clause ℕ} (hc : c ∈ φ.hard ++ φ.soft.map Prod.fst)
    {l : Literal ℕ} (hl : l ∈ c) : l.1 < φ.relaxBase :=
  CNF.lt_dimacsVars (CNF.mem_vars.2 ⟨c, hc, l.2, hl⟩)

private theorem mem_of_mem_zipIdx {p : (Clause ℕ × ℕ) × ℕ} (hp : p ∈ φ.soft.zipIdx) :
    p.1 ∈ φ.soft :=
  List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp)

private theorem lt_relaxBase_soft {cw : Clause ℕ × ℕ} (hcw : cw ∈ φ.soft) {l : Literal ℕ}
    (hl : l ∈ cw.1) : l.1 < φ.relaxBase :=
  lt_relaxBase (List.mem_append_right _ (List.mem_map_of_mem hcw)) hl

private theorem eval_extend_clause {σ : ℕ → Bool} {c : Clause ℕ}
    (hc : ∀ l ∈ c, l.1 < φ.relaxBase) : c.eval (φ.extend σ) = c.eval σ :=
  Clause.eval_congr fun l hl => by simp [extend, hc l hl]

private theorem extend_relax {σ : ℕ → Bool} {i : ℕ} {cw : Clause ℕ × ℕ}
    (h : φ.soft[i]? = some cw) : φ.extend σ (φ.relaxBase + i) = !(cw.1.eval σ) := by
  simp [extend, h]

/-- The cost of `σ`, as a sum over the indexed soft clauses. -/
private theorem cost_eq_sum (σ : ℕ → Bool) :
    (φ.cost σ : ℤ) =
      (φ.soft.zipIdx.map fun p => ((if p.1.1.eval σ then 0 else p.1.2 : ℕ) : ℤ)).sum := by
  rw [cost, Nat.cast_list_sum]
  conv_lhs => rw [← List.zipIdx_map_fst 0 φ.soft]
  simp only [List.map_map, Function.comp_def]

/-- The value of the term and constant `t` at `τ`. -/
private def termValue (τ : ℕ → Bool) (t : (ℕ × ℤ) × ℤ) : ℤ :=
  t.1.2 * ((τ t.1.1).toNat : ℤ) + t.2

private theorem eval_toObjective (τ : ℕ → Bool) :
    φ.toObjective.eval τ =
      (φ.soft.zipIdx.map fun p => termValue τ (softTerm φ.relaxBase p.1 p.2)).sum := by
  simp only [Objective.eval, toObjective, linVal, List.map_map, Function.comp_def, termValue]
  rw [List.sum_map_add]

/-- The objective value of a soft unit clause is its cost. -/
private theorem termValue_unit {b i : ℕ} {cw : Clause ℕ × ℕ} {l : Literal ℕ}
    (hl : unitLit? cw.1 = some l) (τ : ℕ → Bool) :
    termValue τ (softTerm b cw i) = ((if cw.1.eval τ then 0 else cw.2 : ℕ) : ℤ) := by
  obtain ⟨c, w⟩ := cw
  obtain ⟨v, s⟩ := l
  have hc : c = [(v, s)] := unitLit?_eq_some.1 hl
  subst hc
  cases s <;> cases h : τ v <;>
    simp [softTerm, unitLit?, termValue, Clause.eval, Literal.eval, h]

private theorem termValue_relax {b i : ℕ} {cw : Clause ℕ × ℕ} (hl : unitLit? cw.1 = none)
    (τ : ℕ → Bool) :
    termValue τ (softTerm b cw i) = cw.2 * ((τ (b + i)).toNat : ℤ) := by
  simp [softTerm, hl, termValue]

/-! ### Correctness -/

/-- **A feasible assignment extends to a solution of the encoding.** -/
theorem holds_toPBConstrs_extend {σ : ℕ → Bool} (hσ : φ.feasible σ) :
    ∀ c ∈ φ.toPBConstrs, c.Holds (φ.extend σ) := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [Clause.holds_toPB_iff, eval_extend_clause fun l hl =>
      lt_relaxBase (List.mem_append_left _ hd) hl]
    exact (CNF.eval_eq_true_iff ..).1 hσ d hd
  · obtain ⟨⟨cw, i⟩, hp, hc⟩ := List.mem_filterMap.1 hc
    have hcw := mem_of_mem_zipIdx hp
    have hi : φ.soft[i]? = some cw := List.mem_zipIdx_iff_getElem?.1 hp
    simp only [softConstr?] at hc
    split at hc
    · cases hc
    · cases hc
      rw [Clause.holds_toPB_iff, Clause.eval_eq_true_iff]
      cases h : cw.1.eval σ
      · exact ⟨(φ.relaxBase + i, true), by simp, by simp [extend_relax hi, h]⟩
      · obtain ⟨l, hl, hle⟩ := (Clause.eval_eq_true_iff ..).1
          ((eval_extend_clause fun l hl => lt_relaxBase_soft hcw hl).trans h)
        exact ⟨l, List.mem_append_left _ hl, hle⟩

/-- **The objective value of the extension is the cost.** -/
theorem eval_extend (σ : ℕ → Bool) : φ.toObjective.eval (φ.extend σ) = φ.cost σ := by
  rw [eval_toObjective, cost_eq_sum]
  refine congrArg List.sum (List.map_congr_left fun ⟨cw, i⟩ hp => ?_)
  dsimp only
  have hcw := mem_of_mem_zipIdx hp
  have hi : φ.soft[i]? = some cw := List.mem_zipIdx_iff_getElem?.1 hp
  have hev := eval_extend_clause (σ := σ) fun l hl => lt_relaxBase_soft hcw hl
  cases hl : unitLit? cw.1 with
  | some l => rw [termValue_unit hl, hev]
  | none =>
    rw [termValue_relax hl, extend_relax hi]
    cases cw.1.eval σ <;> simp

/-- **A solution of the encoding is feasible.** -/
theorem feasible_of_holds_toPBConstrs {τ : ℕ → Bool} (h : ∀ c ∈ φ.toPBConstrs, c.Holds τ) :
    φ.feasible τ :=
  (CNF.eval_eq_true_iff ..).2 fun d hd =>
    (Clause.holds_toPB_iff τ d).1 (h _ (List.mem_append_left _ (List.mem_map_of_mem hd)))

/-- **The cost of a solution of the encoding is at most its objective value.** -/
theorem cost_le_eval_of_holds_toPBConstrs {τ : ℕ → Bool}
    (h : ∀ c ∈ φ.toPBConstrs, c.Holds τ) : (φ.cost τ : ℤ) ≤ φ.toObjective.eval τ := by
  rw [eval_toObjective, cost_eq_sum]
  refine List.sum_le_sum fun ⟨cw, i⟩ hp => ?_
  dsimp only
  cases hl : unitLit? cw.1 with
  | some l => rw [termValue_unit hl]
  | none =>
    rw [termValue_relax hl]
    have hc : (Clause.toPB (cw.1 ++ [(φ.relaxBase + i, true)])).Holds τ :=
      h _ (List.mem_append_right _ (List.mem_filterMap.2 ⟨(cw, i), hp, by simp [softConstr?, hl]⟩))
    rw [Clause.holds_toPB_iff, Clause.eval_eq_true_iff] at hc
    obtain ⟨l, hl', hle⟩ := hc
    cases he : cw.1.eval τ
    · have hb : τ (φ.relaxBase + i) = true := by
        rcases List.mem_append.1 hl' with hl' | hl'
        · rw [(Clause.eval_eq_true_iff ..).2 ⟨l, hl', hle⟩] at he
          cases he
        · rw [List.mem_singleton.1 hl'] at hle
          simpa [Literal.eval] using hle
      simp [hb]
    · cases τ (φ.relaxBase + i) <;> simp

/-- **The encoding preserves the optimum**: `v` is the least objective value of a solution of
the encoding iff it is the least cost of a feasible assignment. -/
theorem isLeast_eval_iff {v : ℤ} :
    IsLeast (φ.toObjective.eval '' {τ | ∀ c ∈ φ.toPBConstrs, c.Holds τ}) v ↔
      IsLeast ((fun σ => (φ.cost σ : ℤ)) '' {σ | φ.feasible σ}) v := by
  constructor
  · rintro ⟨⟨τ, hτ, rfl⟩, hlb⟩
    refine ⟨⟨τ, feasible_of_holds_toPBConstrs hτ, le_antisymm
      (cost_le_eval_of_holds_toPBConstrs hτ) ?_⟩, ?_⟩
    · change φ.toObjective.eval τ ≤ φ.cost τ
      rw [← eval_extend]
      exact hlb ⟨_, holds_toPBConstrs_extend (feasible_of_holds_toPBConstrs hτ), rfl⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      change φ.toObjective.eval τ ≤ φ.cost σ
      rw [← eval_extend]
      exact hlb ⟨_, holds_toPBConstrs_extend hσ, rfl⟩
  · rintro ⟨⟨σ, hσ, rfl⟩, hlb⟩
    refine ⟨⟨_, holds_toPBConstrs_extend hσ, eval_extend σ⟩, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    exact (hlb ⟨τ, feasible_of_holds_toPBConstrs hτ, rfl⟩).trans
      (cost_le_eval_of_holds_toPBConstrs hτ)

/-- **The encoding has a solution iff the hard clauses are satisfiable.** -/
theorem exists_holds_toPBConstrs_iff :
    (∃ τ, ∀ c ∈ φ.toPBConstrs, c.Holds τ) ↔ φ.hard.Satisfiable :=
  ⟨fun ⟨τ, hτ⟩ => ⟨τ, feasible_of_holds_toPBConstrs hτ⟩,
    fun ⟨_, hσ⟩ => ⟨_, holds_toPBConstrs_extend hσ⟩⟩

/-! ### Size -/

/-- **One constraint per hard clause and per soft clause that is not a unit.** -/
theorem length_toPBConstrs :
    φ.toPBConstrs.length = φ.hard.length + φ.soft.countP fun cw => (unitLit? cw.1).isNone := by
  rw [toPBConstrs, List.length_append, List.length_map, List.length_filterMap_eq_countP]
  conv_rhs => rw [← List.zipIdx_map_fst 0 φ.soft, List.countP_map]
  congr 1
  refine List.countP_congr fun ⟨cw, i⟩ _ => ?_
  cases h : unitLit? cw.1 <;> simp [softConstr?, h]

/-- One objective term per soft clause. -/
theorem length_lin_toObjective : φ.toObjective.lin.length = φ.soft.length := by
  simp [toObjective]

/-- **The variables of the constraints** are variables of the instance, below `relaxBase`, or
the relaxation variables `relaxBase + i` of the soft clauses at indices `i` that are not units. -/
theorem mem_vars_toPBConstrs {c : PBConstr} (hc : c ∈ φ.toPBConstrs) {v : ℕ} (hv : v ∈ c.vars) :
    v < φ.relaxBase ∨ ∃ i cw, φ.soft[i]? = some cw ∧ unitLit? cw.1 = none ∧
      v = φ.relaxBase + i := by
  have hvars (d : Clause ℕ) : v ∈ d.toPB.vars → ∃ l ∈ d, l.1 = v := by
    intro hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ht
    exact ⟨l, List.mem_dedup.1 hl, rfl⟩
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    obtain ⟨l, hl, rfl⟩ := hvars d hv
    exact .inl (lt_relaxBase (List.mem_append_left _ hd) hl)
  · obtain ⟨⟨cw, i⟩, hp, hc⟩ := List.mem_filterMap.1 hc
    simp only [softConstr?] at hc
    split at hc
    · cases hc
    · rename_i hl
      cases hc
      obtain ⟨l, hl', rfl⟩ := hvars _ hv
      rcases List.mem_append.1 hl' with hl' | hl'
      · exact .inl (lt_relaxBase_soft (mem_of_mem_zipIdx hp) hl')
      · rw [List.mem_singleton.1 hl']
        exact .inr ⟨i, cw, List.mem_zipIdx_iff_getElem?.1 hp, hl, rfl⟩

/-- **The variables of the objective** are variables of the instance, below `relaxBase`, or
the relaxation variables `relaxBase + i` of the soft clauses at indices `i` that are not units. -/
theorem mem_lin_toObjective {e : ℕ × ℤ} (he : e ∈ φ.toObjective.lin) :
    e.1 < φ.relaxBase ∨ ∃ i cw, φ.soft[i]? = some cw ∧ unitLit? cw.1 = none ∧
      e.1 = φ.relaxBase + i := by
  obtain ⟨⟨cw, i⟩, hp, rfl⟩ := List.mem_map.1 he
  have hcw := mem_of_mem_zipIdx hp
  cases hl : unitLit? cw.1 with
  | some l =>
    obtain ⟨v, s⟩ := l
    have hc := unitLit?_eq_some.1 hl
    have hlt := lt_relaxBase_soft hcw (l := (v, s)) (by simp [hc])
    left
    cases s <;> simpa [softTerm, hl] using hlt
  | none => exact .inr ⟨i, cw, List.mem_zipIdx_iff_getElem?.1 hp, hl, by simp [softTerm, hl]⟩

/-! ### Certified optima -/

variable {P : RedProof} {pres : Option (List ℕ)} {q : ℕ} {asg : Option (List (Literal ℕ))}

/-- **Soundness for the lower bound**: if the checker accepts `conclusion BOUNDS lb : q ub` for
the encoding, then every feasible assignment has cost at least `lb`. -/
theorem le_cost_of_checkRed {lb : ℤ} {ub : Option ℤ}
    (h : checkRed φ.toPBConstrs (some φ.toObjective) P pres = true)
    (hc : P.conclusion = .bounds (some lb) q ub asg) {σ : ℕ → Bool} (hσ : φ.feasible σ) :
    lb ≤ φ.cost σ := by
  rw [← eval_extend]
  exact le_eval_of_checkRed h hc _ (holds_toPBConstrs_extend hσ)

/-- **Soundness for the upper bound**: if the checker accepts `conclusion BOUNDS lb : q ub` with
a finite `ub` for the encoding, then some feasible assignment has cost at most `ub`. With
`Cslib.Logic.PL.MaxSAT.le_cost_of_checkRed`, the MaxSAT optimum lies in `[lb, ub]`. -/
theorem exists_cost_le_of_checkRed {lb : Option ℤ} {ub : ℤ}
    (h : checkRed φ.toPBConstrs (some φ.toObjective) P pres = true)
    (hc : P.conclusion = .bounds lb q (some ub) asg) :
    ∃ σ, φ.feasible σ ∧ (φ.cost σ : ℤ) ≤ ub := by
  obtain ⟨τ, hτ, hle⟩ := exists_eval_le_of_checkRed h hc
  exact ⟨τ, feasible_of_holds_toPBConstrs hτ, (cost_le_eval_of_holds_toPBConstrs hτ).trans hle⟩

/-- **Soundness for `BOUNDS INF`**: if the checker accepts `conclusion BOUNDS INF : q ub` for the
encoding, then the hard clauses are unsatisfiable. -/
theorem not_satisfiable_of_checkRed_bounds {ub : Option ℤ}
    (h : checkRed φ.toPBConstrs (some φ.toObjective) P pres = true)
    (hc : P.conclusion = .bounds none q ub asg) : ¬ φ.hard.Satisfiable := fun ⟨_, hσ⟩ =>
  VeriPB.not_satisfiable_of_checkRed_bounds h hc _ (holds_toPBConstrs_extend hσ)

/-- **Soundness for the optimum**: if the checker accepts `conclusion BOUNDS v : q v` for the
encoding, then `v` is the least cost of a feasible assignment. -/
theorem isLeast_cost_of_checkRed {v : ℤ}
    (h : checkRed φ.toPBConstrs (some φ.toObjective) P pres = true)
    (hc : P.conclusion = .bounds (some v) q (some v) asg) :
    IsLeast ((fun σ => (φ.cost σ : ℤ)) '' {σ | φ.feasible σ}) v := by
  obtain ⟨σ, hσ, hle⟩ := exists_cost_le_of_checkRed h hc
  refine ⟨⟨σ, hσ, le_antisymm hle (le_cost_of_checkRed h hc hσ)⟩, ?_⟩
  rintro _ ⟨τ, hτ, rfl⟩
  exact le_cost_of_checkRed h hc hτ

/-- **`v` is the MaxSAT optimum iff the checker accepts some proof of `BOUNDS v : q v` for the
encoding**, for every preserved set: soundness, and the completeness of the checker
(`Cslib.Logic.PL.VeriPB.isLeast_iff_exists_checkRed_bounds`). -/
theorem isLeast_cost_iff_exists_checkRed_bounds {v : ℤ} :
    IsLeast ((fun σ => (φ.cost σ : ℤ)) '' {σ | φ.feasible σ}) v ↔
      ∃ (P : RedProof) (q : ℕ), P.conclusion = .bounds (some v) q (some v) none ∧
        checkRed φ.toPBConstrs (some φ.toObjective) P pres = true :=
  isLeast_eval_iff.symm.trans isLeast_iff_exists_checkRed_bounds

/-- **Completeness for the optimum**: if the hard clauses are satisfiable, there is a least cost
`v` of a feasible assignment, and the checker accepts some proof of `BOUNDS v : q v` for the
encoding, for every preserved set. -/
theorem exists_checkRed_bounds (hφ : φ.hard.Satisfiable) :
    ∃ v : ℕ, IsLeast ((fun σ => (φ.cost σ : ℤ)) '' {σ | φ.feasible σ}) v ∧
      ∃ (P : RedProof) (q : ℕ), P.conclusion = .bounds (some v) q (some v) none ∧
        checkRed φ.toPBConstrs (some φ.toObjective) P pres = true := by
  classical
  obtain ⟨σ, hσ⟩ := hφ
  have hex : ∃ k, ∃ σ, φ.feasible σ ∧ φ.cost σ = k := ⟨_, σ, hσ, rfl⟩
  obtain ⟨τ, hτ, hk⟩ := Nat.find_spec hex
  have hleast : IsLeast ((fun σ => (φ.cost σ : ℤ)) '' {σ | φ.feasible σ}) (Nat.find hex) :=
    ⟨⟨τ, hτ, by simp [hk]⟩, by
      rintro _ ⟨ρ, hρ, rfl⟩
      change (Nat.find hex : ℤ) ≤ φ.cost ρ
      exact_mod_cast Nat.find_min' hex ⟨ρ, hρ, rfl⟩⟩
  exact ⟨_, hleast, isLeast_cost_iff_exists_checkRed_bounds.1 hleast⟩

/-- **The hard clauses are unsatisfiable iff the checker accepts some proof of `BOUNDS INF` for
the encoding**, for every preserved set: soundness, and the completeness of the checker
(`Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_checkRed_boundsInf`). -/
theorem not_satisfiable_iff_exists_checkRed_boundsInf :
    ¬ φ.hard.Satisfiable ↔
      ∃ (P : RedProof) (q : ℕ), P.conclusion = .bounds none q none none ∧
        checkRed φ.toPBConstrs (some φ.toObjective) P pres = true := by
  rw [← exists_holds_toPBConstrs_iff]
  exact VeriPB.not_satisfiable_iff_exists_checkRed_boundsInf

end Cslib.Logic.PL.MaxSAT

end
