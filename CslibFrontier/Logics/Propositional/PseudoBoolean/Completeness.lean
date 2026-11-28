/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.CompileCuttingPlanes
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
-- `import all`: the constructions run `soli` and `solx` steps, unfolding the unexposed `stepTop`
-- and `State.log` and the private `State.addCore`, `State.improve` and `lowerTo`, and read the
-- input database back through the private `holds_of_allHold_initDb`.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import CslibFrontier.Logics.Propositional.CuttingPlanes.Completeness
import Mathlib.Data.Set.Finite.List

/-!
# Completeness of the VeriPB kernel checker

The kernel checker is sound for every conclusion (`Cslib.Logic.PL.VeriPB.not_satisfiable_of_check`,
`Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed`,
`Cslib.Logic.PL.VeriPB.exists_satisfies_of_checkRed`, `Cslib.Logic.PL.VeriPB.le_eval_of_checkRed`,
`Cslib.Logic.PL.VeriPB.exists_eval_le_of_checkRed`,
`Cslib.Logic.PL.VeriPB.encard_eq_of_checkRed_enumComplete`). This module proves the converse:
every true conclusion has a proof that the checker accepts. The proofs are existence results and
may be exponentially long in the number of variables.

**Refuting a database.** Every database without a 0/1 solution, with distinct numbers below the
next number, is refuted by `pol` steps without saturation
(`Cslib.Logic.PL.VeriPB.exists_runSteps_contra`): cutting planes refute the inequalities of its
constraints (`Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_of_not_exists_holds`), and the
refutation compiles into one `pol` step per line
(`Cslib.Logic.PL.VeriPB.exists_runSteps_of_isProof`). Run from any state of `checkRed`, these steps
change only the database and the next number
(`Cslib.Logic.PL.VeriPB.runTop_map_step_of_ne_del`). Every construction below ends with such a
refutation.

**Logged solutions.** The kernel format does not propagate a logged solution: its literals must
satisfy every constraint of the database on their own (`Cslib.Logic.PL.VeriPB.solves`). The
constructions log `Cslib.Logic.PL.VeriPB.solutionOf vs σ`, the full assignment of a solution `σ` to
a list `vs` of variables that contains the variables of the formula, and also those of the
objective for `soli` and those of the preserved set for `solx`. Normalization introduces no
variable (`Cslib.Logic.PL.PBConstr.mem_vars_of_mem_vars_normalize`), so these literals decide every
constraint of the database (`Cslib.Logic.PL.VeriPB.solves_solutionOf`).

**The conclusions.**
* `UNSAT`: an unsatisfiable formula has a checked proof made of `pol` steps
  (`Cslib.Logic.PL.VeriPB.exists_check_of_not_satisfiable`), also under `checkRed` with any
  objective and preserved set (`Cslib.Logic.PL.VeriPB.exists_checkRed_unsat_of_not_satisfiable`).
  So a formula is unsatisfiable iff the checker accepts some proof of `UNSAT`
  (`Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_check`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_checkRed_unsat`).
* `SAT : ρ`: the empty proof with the full assignment of a solution
  (`Cslib.Logic.PL.VeriPB.checkRed_sat_solutionOf`). So a formula is satisfiable iff the checker
  accepts some proof of `SAT` (`Cslib.Logic.PL.VeriPB.satisfiable_iff_exists_checkRed_sat`).
* `BOUNDS v : q v`: for an optimal solution `σ` of value `v`, `soli` logs `σ`, adding the
  improving constraint `f ≤ v - 1`, and the database, which now has no solution, is refuted
  (`Cslib.Logic.PL.VeriPB.exists_checkRed_bounds_of_isOptimal`). So `v` is the optimum iff the
  checker accepts some `BOUNDS v : q v`
  (`Cslib.Logic.PL.VeriPB.isLeast_iff_exists_checkRed_bounds`).
  An unsatisfiable formula gets `BOUNDS INF : q INF` made of `pol` steps
  (`Cslib.Logic.PL.VeriPB.exists_checkRed_boundsInf_of_not_satisfiable`), so a formula is
  unsatisfiable iff the checker accepts some `BOUNDS INF : q INF`
  (`Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_checkRed_boundsInf`).
* `ENUMERATION_COMPLETE n : q`: `solx` logs one solution per projection to the preserved set,
  each adding its solution-excluding constraint, and the database, which then has no solution, is
  refuted. The projections of the solutions of a formula are always finite in number, and their
  number is `n` iff the checker accepts some `ENUMERATION_COMPLETE n : q`
  (`Cslib.Logic.PL.VeriPB.encard_eq_iff_exists_checkRed_enumComplete`).

For CNFs, `UNSAT` completeness also follows from the embedding of LRAT proofs
(`Cslib.Logic.PL.CNF.exists_check_iff`); the route here goes through cutting planes and covers
every pseudo-Boolean formula and every objective and preserved set.

## Main definitions

* `Cslib.Logic.PL.VeriPB.solutionOf`: the full assignment of `σ` to a list of variables, as a
  list of literals.

## Main results

* `Cslib.Logic.PL.VeriPB.exists_check_of_not_satisfiable`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_check`,
  `Cslib.Logic.PL.VeriPB.exists_checkRed_unsat_of_not_satisfiable`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_checkRed_unsat`: `UNSAT` completeness.
* `Cslib.Logic.PL.VeriPB.checkRed_sat_solutionOf`,
  `Cslib.Logic.PL.VeriPB.satisfiable_iff_exists_checkRed_sat`: `SAT` completeness.
* `Cslib.Logic.PL.VeriPB.exists_checkRed_bounds_of_isOptimal`,
  `Cslib.Logic.PL.VeriPB.isLeast_iff_exists_checkRed_bounds`,
  `Cslib.Logic.PL.VeriPB.exists_checkRed_boundsInf_of_not_satisfiable`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_checkRed_boundsInf`: `BOUNDS` completeness.
* `Cslib.Logic.PL.VeriPB.exists_checkRed_enumComplete_of_sols`,
  `Cslib.Logic.PL.VeriPB.encard_eq_iff_exists_checkRed_enumComplete`: `ENUMERATION_COMPLETE`
  completeness.
-/

public section

namespace Cslib.Logic.PL

open PBConstr CuttingPlanes

namespace VeriPB

/-! ### Refuting a database -/

/-- **Every database without a solution is refuted by `pol` steps.** A database `db` with distinct
numbers below `n` and no 0/1 solution has a cutting planes refutation, which compiles into `pol`
steps without saturation, one per line (`Cslib.Logic.PL.VeriPB.CPLine.toStep`), that run from `db`
and reach a database naming a contradiction. -/
theorem exists_runSteps_contra {db : List (ℕ × PBConstr)} {n : ℕ} (hid : IdOk db n)
    (h : ¬ ∃ σ, AllHold σ db) :
    ∃ (ann : List CPLine) (db' : List (ℕ × PBConstr)) (n' : ℕ),
      runSteps db n (ann.map (CPLine.toStep n)) = some (db', n') ∧ ∃ q, namesContra db' q := by
  obtain ⟨_, ls, hls, hcontra, -⟩ := exists_refutableInSize_toIneq_iff.2 fun ⟨σ, hσ⟩ =>
    h ⟨σ, fun e he => hσ e.2 (List.mem_map_of_mem he)⟩
  obtain ⟨ann, E, -, hrun, -, hrep⟩ := exists_runSteps_of_isProof hid.lt (fun I hI => by
    obtain ⟨c, hc, rfl⟩ := hI
    obtain ⟨⟨i, c⟩, he, rfl⟩ := List.mem_map.1 hc
    exact ⟨i, c, hid.lookup_eq he, dominates_toIneq c⟩) hls
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 (List.mem_reverse.2 hcontra)
  obtain ⟨c, hc, hcI⟩ := hrep p _ hp
  refine ⟨ann, E ++ db, _, hrun, n + p, ?_⟩
  simp only [namesContra, hc, Option.any_some, decide_eq_true_eq]
  exact hcI.isContradiction

/-- Implicational steps other than deletions change only the database and the next number of a
state of `checkRed`. -/
theorem runTop_map_step_of_ne_del (F : List PBConstr) (obj : Option Objective) (s : State)
    (ss : List Step) (hss : ∀ st ∈ ss, ∀ ids, st ≠ .del ids) :
    runTop F obj s (ss.map .step) =
      (runSteps s.db s.next ss).map fun r => { s with db := r.1, next := r.2 } := by
  induction ss generalizing s with
  | nil => simp [runTop_nil, runSteps]
  | cons st ss ih =>
    rw [List.map_cons, runTop_cons, stepTop_step_of_ne_del F obj s (hss st (by simp))]
    simp only [runSteps]
    rcases runStep s.db s.next st with _ | ⟨db', n'⟩
    · rfl
    · exact ih _ fun st h => hss st (List.mem_cons_of_mem _ h)

/-- **Every state whose database has no solution is refuted by `pol` steps**, which change only
its database and next number. -/
theorem exists_runTop_contra (F : List PBConstr) (obj : Option Objective) (s : State)
    (hid : IdOk s.db s.next) (h : ¬ ∃ σ, AllHold σ s.db) :
    ∃ ss : List Step, ss.all Step.IsCP ∧ ∃ (db' : List (ℕ × PBConstr)) (n' : ℕ),
      runTop F obj s (ss.map .step) = some { s with db := db', next := n' } ∧
        ∃ q, namesContra db' q := by
  obtain ⟨ann, db', n', hrun, hq⟩ := exists_runSteps_contra hid h
  refine ⟨ann.map (CPLine.toStep s.next), by simp [CPLine.isCP_toStep], db', n', ?_, hq⟩
  rw [runTop_map_step_of_ne_del, hrun]
  · rfl
  · intro st hst ids
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hst
    obtain ⟨ops, hops, -⟩ := CPLine.exists_toStep_eq_pol s.next l
    rw [hops]
    exact Step.noConfusion

/-! ### `UNSAT` -/

/-- **`UNSAT` completeness of the kernel checker**: every unsatisfiable formula has a proof made of
cutting planes steps that the checker accepts. -/
theorem exists_check_of_not_satisfiable {F : List PBConstr}
    (h : ¬ ∃ σ, ∀ c ∈ F, c.Holds σ) : ∃ P : Proof, check F P = true ∧ P.steps.all Step.IsCP :=
  exists_check_iff_exists_refutableInSize.2 (exists_refutableInSize_toIneq_iff.2 h)

/-- **A formula is unsatisfiable iff the checker accepts a proof of `UNSAT`.** -/
theorem not_satisfiable_iff_exists_check {F : List PBConstr} :
    (¬ ∃ σ, ∀ c ∈ F, c.Holds σ) ↔ ∃ P : Proof, check F P = true :=
  ⟨fun h => (exists_check_of_not_satisfiable h).imp fun _ h => h.1,
    fun ⟨_, hP⟩ ⟨σ, hσ⟩ => not_satisfiable_of_check hP σ hσ⟩

/-- **`UNSAT` completeness under `checkRed`**: for every objective and preserved set, an
unsatisfiable formula has an accepted proof of `UNSAT` made of cutting planes steps. -/
theorem exists_checkRed_unsat_of_not_satisfiable {F : List PBConstr} (obj : Option Objective)
    (pres : Option (List ℕ)) (h : ¬ ∃ σ, ∀ c ∈ F, c.Holds σ) :
    ∃ (ss : List Step) (q : ℕ), ss.all Step.IsCP ∧
      checkRed F obj ⟨ss.map .step, .unsat q⟩ pres = true := by
  obtain ⟨ss, hcp, db', n', hrun, q, hq⟩ := exists_runTop_contra F obj (State.init F obj pres)
    (idOk_initDb F) fun ⟨σ, hσ⟩ => h ⟨σ, holds_of_allHold_initDb hσ⟩
  refine ⟨ss, q, hcp, ?_⟩
  unfold checkRed
  rw [hrun]
  simp [checkConclusion, State.init, hq]

/-- **A formula is unsatisfiable iff `checkRed` accepts a proof of `UNSAT`**, for every objective
and preserved set. -/
theorem not_satisfiable_iff_exists_checkRed_unsat {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} :
    (¬ ∃ σ, ∀ c ∈ F, c.Holds σ) ↔
      ∃ (P : RedProof) (q : ℕ), P.conclusion = .unsat q ∧ checkRed F obj P pres = true := by
  refine ⟨fun h => ?_, fun ⟨P, q, hc, hP⟩ ⟨σ, hσ⟩ => not_satisfiable_of_checkRed hP hc σ hσ⟩
  obtain ⟨ss, q, -, hP⟩ := exists_checkRed_unsat_of_not_satisfiable obj pres h
  exact ⟨_, q, rfl, hP⟩

/-! ### Full assignments as logged solutions -/

/-- **The full assignment** of `σ` to the variables `vs`: the literal of each variable of `vs`
that is true under `σ`. -/
@[expose]
def solutionOf (vs : List ℕ) (σ : ℕ → Bool) : List (Literal ℕ) := vs.map fun v => (v, σ v)

theorem mem_solutionOf {vs : List ℕ} {σ : ℕ → Bool} {l : Literal ℕ} :
    l ∈ solutionOf vs σ ↔ l.1 ∈ vs ∧ σ l.1 = l.2 := by
  obtain ⟨v, b⟩ := l
  simp [solutionOf]

theorem contains_solutionOf {vs : List ℕ} {σ : ℕ → Bool} {l : Literal ℕ} (hv : l.1 ∈ vs) :
    (solutionOf vs σ).contains l = Literal.eval σ l := by
  obtain ⟨v, b⟩ := l
  simp [mem_solutionOf, Literal.eval, hv, Bool.beq_eq_decide_eq]

/-- The full assignment of `σ` assigns the variables of `vs` as `σ` does. -/
theorem assignOf_solutionOf {vs : List ℕ} {σ : ℕ → Bool} {v : ℕ} (hv : v ∈ vs) :
    assignOf (solutionOf vs σ) v = σ v := by
  rw [assignOf, contains_solutionOf hv]
  simp [Literal.eval]

theorem assignsAll_solutionOf {vs P : List ℕ} {σ : ℕ → Bool} (hP : ∀ x ∈ P, x ∈ vs) :
    assignsAll (solutionOf vs σ) P = true := by
  simp only [assignsAll, List.all_eq_true, Bool.or_eq_true]
  intro x hx
  rw [contains_solutionOf (hP x hx), contains_solutionOf (hP x hx)]
  cases h : σ x <;> simp [Literal.eval, h]

/-- **The full assignment of a solution solves the constraints** whose variables it assigns. -/
theorem solves_solutionOf {vs : List ℕ} {σ : ℕ → Bool} {cs : List PBConstr}
    (h : ∀ c ∈ cs, c.Holds σ ∧ c.vars ⊆ vs) :
    solves (solutionOf vs σ) cs = true := by
  simp only [solves, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    decide_eq_true_eq]
  refine ⟨fun ⟨v, b⟩ hl => ?_, fun c hc => ?_⟩
  · simp_all [mem_solutionOf, Std.Sat.Literal.negate]
  · obtain ⟨hc, hvs⟩ := h c hc
    rw [List.filter_congr fun t ht => contains_solutionOf (by
      obtain ⟨a, v, b⟩ := t
      exact hvs (List.mem_map_of_mem ht)), ← lhs_eq_coeffSum_filter]
    exact hc

/-- The full assignment of a solution of `F` solves the input database. -/
theorem solves_initDb {vs : List ℕ} {σ : ℕ → Bool} {F : List PBConstr}
    (hvs : ∀ c ∈ F, c.vars ⊆ vs) (hσ : ∀ c ∈ F, c.Holds σ) :
    solves (solutionOf vs σ) (F.map normalize) = true := by
  refine solves_solutionOf fun c hc => ?_
  obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
  exact ⟨(holds_normalize σ c).2 (hσ c hc'), fun _ hx =>
    hvs c hc' (mem_vars_of_mem_vars_normalize hx)⟩

private theorem map_snd_initDb (F : List PBConstr) : (initDb F).map (·.2) = F.map normalize := by
  simp only [initDb, List.map_map]
  rw [show ((·.2) ∘ fun e : PBConstr × ℕ => (e.2 + 1, e.1.normalize)) = normalize ∘ Prod.fst
    from rfl, ← List.map_map, List.zipIdx_map_fst]

/-! ### `SAT` -/

/-- **`SAT` completeness**: the empty proof with conclusion `SAT : ρ`, for the full assignment `ρ`
of a solution to a list of variables containing those of the formula, is accepted. -/
theorem checkRed_sat_solutionOf {F : List PBConstr} {vs : List ℕ} {σ : ℕ → Bool}
    (obj : Option Objective) (pres : Option (List ℕ))
    (hvs : ∀ c ∈ F, c.vars ⊆ vs) (hσ : ∀ c ∈ F, c.Holds σ) :
    checkRed F obj ⟨[], .sat (some (solutionOf vs σ))⟩ pres = true := by
  simp only [checkRed, runTop_nil, checkConclusion]
  exact solves_initDb hvs hσ

/-- **A formula is satisfiable iff the checker accepts a proof of `SAT`**, for every objective and
preserved set. -/
theorem satisfiable_iff_exists_checkRed_sat {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} :
    (∃ σ, ∀ c ∈ F, c.Holds σ) ↔ ∃ (P : RedProof) (asg : Option (List (Literal ℕ))),
      P.conclusion = .sat asg ∧ checkRed F obj P pres = true :=
  ⟨fun ⟨_, hσ⟩ => ⟨_, _, rfl, checkRed_sat_solutionOf (vs := F.flatMap PBConstr.vars) obj pres
      (fun c hc _ hx => List.mem_flatMap.2 ⟨c, hc, hx⟩) hσ⟩,
    fun ⟨_, _, hc, hP⟩ => exists_satisfies_of_checkRed hP hc⟩

/-! ### `BOUNDS` -/

/-- The objective at the full assignment of `σ` to its variables is its value at `σ`. -/
theorem eval_assignOf_solutionOf {vs : List ℕ} {σ : ℕ → Bool} {f : Objective}
    (hf : ∀ e ∈ f.lin, e.1 ∈ vs) : f.eval (assignOf (solutionOf vs σ)) = f.eval σ := by
  rw [Objective.eval, Objective.eval,
    linVal_congr fun e he => assignOf_solutionOf (σ := σ) (hf e he)]

/-- **`BOUNDS` completeness**: let `σ` be an optimal solution of `F` for the objective `f`, of value
`v`, and `vs` a list of variables containing those of `F` and of `f`. The proof that logs the full
assignment of `σ` to `vs` by `soli`, adding the improving constraint `f ≤ v - 1`, and then refutes
the database by cutting planes steps is accepted with conclusion `BOUNDS v : q v`. -/
theorem exists_checkRed_bounds_of_isOptimal {F : List PBConstr} {f : Objective} {σ : ℕ → Bool}
    {vs : List ℕ} (pres : Option (List ℕ)) (hvs : ∀ c ∈ F, c.vars ⊆ vs)
    (hf : ∀ e ∈ f.lin, e.1 ∈ vs) (hσ : ∀ c ∈ F, c.Holds σ)
    (hopt : ∀ τ, (∀ c ∈ F, c.Holds τ) → f.eval σ ≤ f.eval τ) :
    ∃ (ss : List Step) (q : ℕ), ss.all Step.IsCP ∧
      checkRed F (some f) ⟨.soli (solutionOf vs σ) :: ss.map .step,
        .bounds (some (f.eval σ)) q (some (f.eval σ)) none⟩ pres = true := by
  set ρ := solutionOf vs σ
  set s₀ := State.init F (some f) pres
  set s₁ := (s₀.log F (some f) ρ).improve f (f.eval (assignOf ρ))
  have hval : f.eval (assignOf ρ) = f.eval σ := eval_assignOf_solutionOf hf
  have hstep : stepTop F (some f) s₀ (.soli ρ) = some s₁ := by
    have ha : assigns ρ f = true := assignsAll_solutionOf (List.forall_mem_map.2 hf)
    simpa [stepTop, s₁, s₀, State.init, map_snd_initDb, ha] using solves_initDb hvs hσ
  have hid : IdOk s₁.db s₁.next := (idOk_initDb F).cons le_rfl _
  obtain ⟨ss, hcp, db', n', hrun, q, hq⟩ := exists_runTop_contra F (some f) s₁ hid
    fun ⟨τ, hτ⟩ => by
      have himp := (holds_normalize τ _).1 (hτ _ (List.mem_cons_self ..))
      rw [Objective.holds_improving, hval] at himp
      exact absurd (hopt τ (holds_of_allHold_initDb fun e he =>
        hτ e (List.mem_cons_of_mem _ he))) (not_le.2 himp)
  refine ⟨ss, q, hcp, ?_⟩
  rw [checkRed, runTop_cons, hstep, Option.bind_some, hrun]
  simp [checkConclusion, s₁, s₀, State.improve, State.addCore, State.log, State.init, lowerTo,
    objValue, boundsOk, hq, hval]

/-- **`v` is the optimum of `f` on the solutions of `F` iff the checker accepts some proof of
`BOUNDS v : q v`**, for every preserved set. -/
theorem isLeast_iff_exists_checkRed_bounds {F : List PBConstr} {f : Objective} {v : ℤ}
    {pres : Option (List ℕ)} :
    IsLeast (f.eval '' {σ | ∀ c ∈ F, c.Holds σ}) v ↔
      ∃ (P : RedProof) (q : ℕ), P.conclusion = .bounds (some v) q (some v) none ∧
        checkRed F (some f) P pres = true := by
  constructor
  · rintro ⟨⟨σ, hσ, rfl⟩, hlb⟩
    obtain ⟨ss, q, -, hP⟩ := exists_checkRed_bounds_of_isOptimal pres
      (vs := F.flatMap PBConstr.vars ++ f.lin.map (·.1))
      (fun c hc _ hx => List.mem_append_left _ (List.mem_flatMap.2 ⟨c, hc, hx⟩))
      (fun e he => List.mem_append_right _ (List.mem_map_of_mem he)) hσ
      fun τ hτ => hlb ⟨τ, hτ, rfl⟩
    exact ⟨_, q, rfl, hP⟩
  · rintro ⟨P, q, hc, hP⟩
    obtain ⟨σ, hσ, hle⟩ := exists_eval_le_of_checkRed hP hc
    exact ⟨⟨σ, hσ, le_antisymm hle (le_eval_of_checkRed hP hc σ hσ)⟩,
      Set.forall_mem_image.2 (le_eval_of_checkRed hP hc)⟩

/-- **`BOUNDS INF` completeness**: for every objective and preserved set, an unsatisfiable formula
has an accepted proof of `BOUNDS INF : q INF` made of cutting planes steps. -/
theorem exists_checkRed_boundsInf_of_not_satisfiable {F : List PBConstr} (f : Objective)
    (pres : Option (List ℕ)) (h : ¬ ∃ σ, ∀ c ∈ F, c.Holds σ) :
    ∃ (ss : List Step) (q : ℕ), ss.all Step.IsCP ∧
      checkRed F (some f) ⟨ss.map .step, .bounds none q none none⟩ pres = true := by
  obtain ⟨ss, hcp, db', n', hrun, q, hq⟩ := exists_runTop_contra F (some f)
    (State.init F (some f) pres) (idOk_initDb F) fun ⟨σ, hσ⟩ =>
      h ⟨σ, holds_of_allHold_initDb hσ⟩
  refine ⟨ss, q, hcp, ?_⟩
  unfold checkRed
  rw [hrun]
  simp [checkConclusion, State.init, boundsOk, hq]

/-- **A formula is unsatisfiable iff the checker accepts a proof of `BOUNDS INF : q INF`**, for
every objective and preserved set. -/
theorem not_satisfiable_iff_exists_checkRed_boundsInf {F : List PBConstr} {f : Objective}
    {pres : Option (List ℕ)} :
    (¬ ∃ σ, ∀ c ∈ F, c.Holds σ) ↔
      ∃ (P : RedProof) (q : ℕ), P.conclusion = .bounds none q none none ∧
        checkRed F (some f) P pres = true := by
  refine ⟨fun h => ?_, fun ⟨_, _, hc, hP⟩ ⟨σ, hσ⟩ =>
    not_satisfiable_of_checkRed_bounds hP hc σ hσ⟩
  obtain ⟨ss, q, -, hP⟩ := exists_checkRed_boundsInf_of_not_satisfiable f pres h
  exact ⟨_, q, rfl, hP⟩

/-! ### `ENUMERATION_COMPLETE` -/

/-- The states from which `solx` steps can be taken: the preserved set is `Pres`, there is no
objective, no unchecked deletion and no change of the preserved set, the numbers are fresh, and the
constraints are over the variables `vs`. -/
private structure SolxReady (Pres vs : List ℕ) (s : State) : Prop where
  pres : s.pres = some Pres
  obj : s.obj = none
  chk : s.chk = true
  presChanged : s.presChanged = false
  idOk : IdOk s.db s.next
  vars : ∀ e ∈ s.db, e.2.vars ⊆ vs

/-- Logging solutions with distinct projections by `solx`, from a state where they solve the
database, adds one projection each and excludes their projections from the solutions of the
database. -/
private theorem exists_runTop_solx {F : List PBConstr} {Pres vs : List ℕ}
    (hP : ∀ x ∈ Pres, x ∈ vs) :
    ∀ (σs : List (ℕ → Bool)) (s : State), SolxReady Pres vs s → (∀ σ ∈ σs, AllHold σ s.db) →
      (σs.map (proj Pres)).Nodup →
      ∃ s', runTop F none s (σs.map fun σ => .solx (solutionOf vs σ)) = some s' ∧
        SolxReady Pres vs s' ∧ s'.logged.length = s.logged.length + σs.length ∧
        ∀ τ, AllHold τ s'.db → AllHold τ s.db ∧ ∀ σ ∈ σs, proj Pres τ ≠ proj Pres σ
  | [], s, hs, _, _ => ⟨s, runTop_nil .., hs, rfl, fun _ h => ⟨h, by simp⟩⟩
  | σ :: σs, s, hs, hσs, hnd => by
    set ρ := solutionOf vs σ
    have hproj : proj Pres (assignOf ρ) = proj Pres σ :=
      List.map_congr_left fun x hx => assignOf_solutionOf (hP x hx)
    set s₁ : State := { (s.log F none ρ).addCore (exclusion Pres ρ) with
      logged := proj Pres (assignOf ρ) :: s.logged }
    have hsol : solves ρ (s.db.map (·.2)) = true := by
      refine solves_solutionOf fun c hc => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      exact ⟨hσs σ (List.mem_cons_self ..) e he, hs.vars e he⟩
    have ha : assignsAll ρ Pres = true := assignsAll_solutionOf hP
    have hstep : stepTop F none s (.solx ρ) = some s₁ := by
      simp [stepTop, hs.pres, hs.obj, hs.chk, hs.presChanged, hsol, ha, s₁]
    have hexcl : ∀ τ, (exclusion Pres ρ).Holds τ ↔ proj Pres τ ≠ proj Pres σ := fun τ => by
      rw [holds_exclusion, hproj]
    have hs₁ : SolxReady Pres vs s₁ :=
      { pres := hs.pres, obj := hs.obj, chk := hs.chk, presChanged := hs.presChanged,
        idOk := hs.idOk.cons le_rfl _
        vars := fun e he x hx => by
          rcases List.mem_cons.1 he with rfl | he
          · simp only [exclusion, PBConstr.vars, List.map_map, List.mem_map] at hx
            obtain ⟨x, hx, rfl⟩ := hx
            exact hP x (List.mem_dedup.1 hx)
          · exact hs.vars e he hx }
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', hrun, hs', hlen, hall⟩ := exists_runTop_solx hP σs s₁ hs₁ (fun σ' hσ' => by
      refine List.forall_mem_cons.2 ⟨(hexcl σ').2 fun h => hnd.1 ?_, hσs σ'
        (List.mem_cons_of_mem _ hσ')⟩
      exact h ▸ List.mem_map_of_mem hσ') hnd.2
    refine ⟨s', by rw [List.map_cons, runTop_cons, hstep, Option.bind_some, hrun], hs', ?_,
      fun τ hτ => ?_⟩
    · rw [hlen]
      simp [s₁]
      omega
    · obtain ⟨hτ₁, hτσs⟩ := hall τ hτ
      refine ⟨fun e he => hτ₁ e (List.mem_cons_of_mem _ he), List.forall_mem_cons.2
        ⟨(hexcl τ).1 (hτ₁ _ (List.mem_cons_self ..)), hτσs⟩⟩

/-- Each projection of a solution is the projection of a chosen solution. -/
private theorem exists_sols_of_projections {F : List PBConstr} {Pres : List ℕ} :
    ∀ ls : List (List Bool), (∀ l ∈ ls, l ∈ projections F Pres) →
      ∃ σs : List (ℕ → Bool), σs.map (proj Pres) = ls ∧ ∀ σ ∈ σs, ∀ c ∈ F, c.Holds σ
  | [], _ => ⟨[], rfl, by simp⟩
  | l :: ls, h => by
    obtain ⟨σ, hσ, rfl⟩ := h l (List.mem_cons_self ..)
    obtain ⟨σs, hσs, hall⟩ := exists_sols_of_projections ls fun l hl =>
      h l (List.mem_cons_of_mem _ hl)
    exact ⟨σ :: σs, by rw [List.map_cons, hσs], List.forall_mem_cons.2 ⟨hσ, hall⟩⟩

/-- The projections of the solutions of a formula to a preserved set are finitely many. -/
theorem finite_projections (F : List PBConstr) (Pres : List ℕ) :
    (projections F Pres).Finite :=
  (List.finite_length_eq Bool Pres.length).subset fun _ ⟨_, _, h⟩ => h ▸ List.length_map _

/-- **`ENUMERATION_COMPLETE` completeness**: let `vs` be a list of variables containing those of
`F` and of the preserved set `Pres`. For any solutions `σs` of `F` whose projections to `Pres` are
distinct and are all the projections of solutions, the proof that logs the full assignment of each
to `vs` by `solx`, each adding its solution-excluding constraint, and then refutes the database by
cutting planes steps is accepted with conclusion `ENUMERATION_COMPLETE n : q`, for the number `n`
of solutions logged. -/
theorem exists_checkRed_enumComplete_of_sols {F : List PBConstr} {Pres vs : List ℕ}
    {σs : List (ℕ → Bool)} (hvs : ∀ c ∈ F, c.vars ⊆ vs)
    (hP : ∀ x ∈ Pres, x ∈ vs) (hσs : ∀ σ ∈ σs, ∀ c ∈ F, c.Holds σ)
    (hnd : (σs.map (proj Pres)).Nodup) (hall : ∀ l ∈ projections F Pres, l ∈ σs.map (proj Pres)) :
    ∃ (ss : List Step) (q : ℕ), ss.all Step.IsCP ∧
      checkRed F none ⟨σs.map (fun σ => .solx (solutionOf vs σ)) ++ ss.map .step,
        .enumComplete σs.length q⟩ (some Pres) = true := by
  set s₀ := State.init F none (some Pres)
  have hs₀ : SolxReady Pres vs s₀ :=
    { pres := rfl, obj := rfl, chk := rfl, presChanged := rfl, idOk := idOk_initDb F
      vars := fun e he x hx => by
        have he' : e.2 ∈ F.map normalize := map_snd_initDb F ▸ List.mem_map_of_mem he
        obtain ⟨c, hc, hce⟩ := List.mem_map.1 he'
        exact hvs c hc (mem_vars_of_mem_vars_normalize (hce ▸ hx)) }
  obtain ⟨s', hrun, hs', hlen, hexcl⟩ := exists_runTop_solx (F := F) hP σs s₀ hs₀
    (fun σ hσ => allHold_initDb (hσs σ hσ)) hnd
  obtain ⟨ss, hcp, db', n', hrun', q, hq⟩ := exists_runTop_contra F none s' hs'.idOk
    fun ⟨τ, hτ⟩ => by
      obtain ⟨hτ₀, hτσs⟩ := hexcl τ hτ
      obtain ⟨σ, hσ, he⟩ := List.mem_map.1 (hall _ ⟨τ, holds_of_allHold_initDb hτ₀, rfl⟩)
      exact hτσs σ hσ he.symm
  refine ⟨ss, q, hcp, ?_⟩
  rw [checkRed, runTop_append, hrun, Option.bind_some, hrun']
  simp [checkConclusion, hs'.pres, hlen, s₀, State.init, hq]

/-- **The solutions of `F` have exactly `n` distinct projections to the preserved set `Pres` iff
the checker accepts some proof of `ENUMERATION_COMPLETE n : q`** without an objective. -/
theorem encard_eq_iff_exists_checkRed_enumComplete {F : List PBConstr} {Pres : List ℕ} {n : ℕ} :
    (projections F Pres).encard = n ↔
      ∃ (P : RedProof) (q : ℕ), P.conclusion = .enumComplete n q ∧
        checkRed F none P (some Pres) = true := by
  refine ⟨fun h => ?_, fun ⟨P, q, hc, hP⟩ => encard_eq_of_checkRed_enumComplete hP hc⟩
  have hfin := finite_projections F Pres
  set ls := hfin.toFinset.toList
  obtain ⟨σs, hσs, hsol⟩ := exists_sols_of_projections (F := F) (Pres := Pres) ls
    fun l hl => hfin.mem_toFinset.1 (Finset.mem_toList.1 hl)
  have hlen : σs.length = n := by
    have := congrArg List.length hσs
    rw [List.length_map, Finset.length_toList] at this
    rw [this]
    exact_mod_cast (hfin.encard_eq_coe_toFinset_card).symm.trans h
  obtain ⟨ss, q, -, hP⟩ := exists_checkRed_enumComplete_of_sols
    (vs := F.flatMap PBConstr.vars ++ Pres)
    (fun c hc _ hx => List.mem_append_left _ (List.mem_flatMap.2 ⟨c, hc, hx⟩))
    (fun x hx => List.mem_append_right _ hx) hsol (hσs ▸ Finset.nodup_toList _)
    fun l hl => hσs ▸ Finset.mem_toList.2 (hfin.mem_toFinset.2 hl)
  exact ⟨_, q, by rw [hlen], hP⟩

end VeriPB

end Cslib.Logic.PL
