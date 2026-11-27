/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.CompileCuttingPlanes
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
public import CslibFrontier.Logics.Propositional.PseudoBoolean.RupRefutation
public import Mathlib.Data.List.MinMax
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
every true conclusion has a proof that the checker accepts, by cutting planes (existence results)
and by executable producers. The proofs may be exponentially long in the number of variables.

**Refuting a database.** Every database without a 0/1 solution, with distinct numbers below the
next number, is refuted by `pol` steps without saturation
(`Cslib.Logic.PL.VeriPB.exists_runSteps_contra`): cutting planes refute the inequalities of its
constraints (`Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_of_not_exists_holds`), and the
refutation compiles into one `pol` step per line
(`Cslib.Logic.PL.VeriPB.exists_runSteps_of_isProof`). Run from any state of `checkRed`, these steps
change only the database and the next number
(`Cslib.Logic.PL.VeriPB.runTop_map_step_of_ne_del`). Every construction below ends with a
refutation of the database it reaches: such a cutting planes refutation, for the existence
results, or the decision tree of `rup` steps over the variables
(`Cslib.Logic.PL.VeriPB.refuteSteps`, `Cslib.Logic.PL.VeriPB.runTop_refuteSteps`), for the
producers. The two share the solution-logging part of each construction.

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

**The producers.** `Cslib.Logic.PL.VeriPB.refutation`, `Cslib.Logic.PL.VeriPB.boundsProof` and
`Cslib.Logic.PL.VeriPB.enumProof` build the proofs of the constructions above with the decision
tree as refutation, given the solutions to log. The search producers find those solutions by trying
all `2 ^ k` assignments of the `k` distinct variables involved
(`Cslib.Logic.PL.VeriPB.solutionsOn`): `Cslib.Logic.PL.VeriPB.refute` (`UNSAT`, a proof of
`2 ^ (k + 1) - 1` `rup` steps of clauses of at most `k` literals with at most three hints each),
`Cslib.Logic.PL.VeriPB.solve` (`SAT : ρ`), `Cslib.Logic.PL.VeriPB.optimize` (`BOUNDS v : q v`, or
`BOUNDS INF : q INF`) and `Cslib.Logic.PL.VeriPB.enumerate` (`ENUMERATION_COMPLETE n : q`). Each is
accepted by the checker (`Cslib.Logic.PL.VeriPB.checkRed_of_refute_eq_some`,
`Cslib.Logic.PL.VeriPB.checkRed_of_solve_eq_some`, `Cslib.Logic.PL.VeriPB.checkRed_optimize`,
`Cslib.Logic.PL.VeriPB.checkRed_enumerate`), and the soundness theorems give the meaning of its
conclusion. The `UNSAT` and `BOUNDS INF` halves of the characterizations
`Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_checkRed_unsat` and
`Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_checkRed_boundsInf` are derived from the
decision-tree proofs.

For CNFs, `UNSAT` completeness also follows from the embedding of LRAT proofs
(`Cslib.Logic.PL.CNF.exists_check_iff`); the route here goes through cutting planes and covers
every pseudo-Boolean formula and every objective and preserved set.

## Main definitions

* `Cslib.Logic.PL.VeriPB.solutionOf`: the full assignment of `σ` to a list of variables, as a
  list of literals.
* `Cslib.Logic.PL.VeriPB.refutation`, `Cslib.Logic.PL.VeriPB.boundsProof`,
  `Cslib.Logic.PL.VeriPB.enumProof`: the proofs of the constructions, refuted by the decision
  tree.
* `Cslib.Logic.PL.VeriPB.assignments`, `Cslib.Logic.PL.VeriPB.solutionsOn`: the assignments of a
  list of variables, and the solutions among them.
* `Cslib.Logic.PL.VeriPB.refute`, `Cslib.Logic.PL.VeriPB.solve`, `Cslib.Logic.PL.VeriPB.optimize`,
  `Cslib.Logic.PL.VeriPB.enumerate`: the producers.

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
* `Cslib.Logic.PL.VeriPB.runTop_refuteSteps`, `Cslib.Logic.PL.VeriPB.checkRed_refutation_unsat`,
  `Cslib.Logic.PL.VeriPB.checkRed_refutation_boundsInf`,
  `Cslib.Logic.PL.VeriPB.checkRed_boundsProof`, `Cslib.Logic.PL.VeriPB.checkRed_enumProof`: the
  decision-tree proofs are accepted.
* `Cslib.Logic.PL.VeriPB.isSome_refute`, `Cslib.Logic.PL.VeriPB.checkRed_of_refute_eq_some`,
  `Cslib.Logic.PL.VeriPB.isSome_solve`, `Cslib.Logic.PL.VeriPB.checkRed_of_solve_eq_some`,
  `Cslib.Logic.PL.VeriPB.checkRed_optimize`, `Cslib.Logic.PL.VeriPB.checkRed_enumerate`: the
  producers answer every instance and are accepted, `refute` with its size.
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

theorem runTop_append (F : List PBConstr) (obj : Option Objective) (s : State)
    (ts ts' : List TopStep) :
    runTop F obj s (ts ++ ts') = (runTop F obj s ts).bind fun s' => runTop F obj s' ts' := by
  induction ts generalizing s with
  | nil => simp [runTop_nil]
  | cons t ts ih =>
    rw [List.cons_append, runTop_cons, runTop_cons]
    rcases stepTop F obj s t with _ | s₁
    · rfl
    · exact ih s₁

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

/-- **Every state whose database has no solution is refuted by the decision tree** of `rup`
steps over a list of variables containing those of the database
(`Cslib.Logic.PL.VeriPB.refuteSteps`), which changes only its database and next number. -/
theorem runTop_refuteSteps (F : List PBConstr) (obj : Option Objective) (s : State)
    {vs : List ℕ} (hid : IdOk s.db s.next) (hvs : ∀ e ∈ s.db, e.2.vars ⊆ vs)
    (h : ¬ ∃ σ, AllHold σ s.db) :
    ∃ db', runTop F obj s ((refuteSteps s.db s.next vs).map .step) =
        some { s with db := db', next := s.next + (2 ^ (vs.length + 1) - 1) } ∧
      namesContra db' (s.next + (2 ^ (vs.length + 1) - 1) - 1) = true := by
  obtain ⟨db', hrun, -, hq⟩ := runSteps_refuteSteps hid hvs h
  refine ⟨db', ?_, hq⟩
  rw [runTop_map_step_of_ne_del, hrun]
  · rfl
  · intro st hst ids
    obtain ⟨K, hs, rfl, -⟩ := exists_eq_rup_of_mem_refuteSteps hst
    exact Step.noConfusion

/-- The steps `pre` run from the initial state to the state `s`, whose database has fresh numbers,
is over the variables `vs` and has no solution, and where the conclusion `c q` is accepted once
the database names the contradiction `q`. Every construction below refutes such a state, by
cutting planes (`Refutable.exists_checkRed`) or by the decision tree
(`Refutable.checkRed_refuteSteps`). -/
private structure Refutable (F : List PBConstr) (obj : Option Objective)
    (pres : Option (List ℕ)) (vs : List ℕ) (pre : List TopStep) (c : ℕ → Conclusion)
    (s : State) : Prop where
  run : runTop F obj (State.init F obj pres) pre = some s
  idOk : IdOk s.db s.next
  vars : ∀ e ∈ s.db, e.2.vars ⊆ vs
  unsat : ¬ ∃ σ, AllHold σ s.db
  concl : ∀ db' n' q, namesContra db' q = true →
    checkConclusion F obj { s with db := db', next := n' } (c q) = true

private theorem Refutable.exists_checkRed {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {vs : List ℕ} {pre : List TopStep} {c : ℕ → Conclusion} {s : State}
    (h : Refutable F obj pres vs pre c s) :
    ∃ (ss : List Step) (q : ℕ), ss.all Step.IsCP ∧
      checkRed F obj ⟨pre ++ ss.map .step, c q⟩ pres = true := by
  obtain ⟨ss, hcp, db', n', hrun, q, hq⟩ := exists_runTop_contra F obj s h.idOk h.unsat
  refine ⟨ss, q, hcp, ?_⟩
  rw [checkRed, runTop_append, h.run, Option.bind_some, hrun]
  exact h.concl _ _ _ hq

private theorem Refutable.checkRed_refuteSteps {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {vs : List ℕ} {pre : List TopStep} {c : ℕ → Conclusion} {s : State}
    (h : Refutable F obj pres vs pre c s) :
    checkRed F obj ⟨pre ++ (refuteSteps s.db s.next vs).map .step,
      c (s.next + (2 ^ (vs.length + 1) - 1) - 1)⟩ pres = true := by
  obtain ⟨db', hrun, hq⟩ := runTop_refuteSteps F obj s h.idOk h.vars h.unsat
  rw [checkRed, runTop_append, h.run, Option.bind_some, hrun]
  exact h.concl _ _ _ hq

/-- The constraints of the input database are over the variables of the formula. -/
private theorem vars_initDb {F : List PBConstr} {vs : List ℕ} (hvs : ∀ c ∈ F, c.vars ⊆ vs) :
    ∀ e ∈ initDb F, e.2.vars ⊆ vs := fun e he x hx => by
  simp only [initDb, List.mem_map] at he
  obtain ⟨⟨c, i⟩, hc, rfl⟩ := he
  exact hvs c (List.fst_mem_of_mem_zipIdx hc) (mem_vars_of_mem_vars_normalize hx)

/-- The initial state of an unsatisfiable formula is refutable, for a conclusion accepted on
every database naming the contradiction, with the initial bounds. -/
private theorem refutable_init {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {vs : List ℕ} (hvs : ∀ c ∈ F, c.vars ⊆ vs)
    (h : ¬ ∃ σ, ∀ c ∈ F, c.Holds σ) {c : ℕ → Conclusion}
    (hc : ∀ db' n' q, namesContra db' q = true →
      checkConclusion F obj { State.init F obj pres with db := db', next := n' } (c q) = true) :
    Refutable F obj pres vs [] c (State.init F obj pres) :=
  ⟨runTop_nil .., idOk_initDb F, vars_initDb hvs,
    fun ⟨σ, hσ⟩ => h ⟨σ, holds_of_allHold_initDb hσ⟩, hc⟩

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
  simpa using (refutable_init (obj := obj) (pres := pres) (vs := F.flatMap PBConstr.vars)
    (fun c hc _ hx => List.mem_flatMap.2 ⟨c, hc, hx⟩) h (c := .unsat)
    fun _ _ _ hq => by simp [checkConclusion, State.init, hq]).exists_checkRed

/-- **The decision-tree refutation** of `F` over the variables `vs`, with the conclusion `c q` for
the number `q` of its contradiction: `2 ^ (|vs| + 1) - 1` `rup` steps
(`Cslib.Logic.PL.VeriPB.refuteSteps`) from the input database. -/
@[expose]
def refutation (F : List PBConstr) (vs : List ℕ) (c : ℕ → Conclusion) : RedProof :=
  ⟨(refuteSteps (initDb F) (F.length + 1) vs).map .step,
    c (F.length + 1 + (2 ^ (vs.length + 1) - 1) - 1)⟩

/-- **The decision-tree refutation proves `UNSAT`** of an unsatisfiable formula over the
variables `vs`, for every objective and preserved set. -/
theorem checkRed_refutation_unsat {F : List PBConstr} {vs : List ℕ} (obj : Option Objective)
    (pres : Option (List ℕ)) (hvs : ∀ c ∈ F, c.vars ⊆ vs) (h : ¬ ∃ σ, ∀ c ∈ F, c.Holds σ) :
    checkRed F obj (refutation F vs .unsat) pres = true := by
  simpa [State.init, refutation] using (refutable_init (obj := obj) (pres := pres) hvs h
    (c := .unsat)
    fun _ _ _ hq => by simp [checkConclusion, State.init, hq]).checkRed_refuteSteps

/-- **A formula is unsatisfiable iff `checkRed` accepts a proof of `UNSAT`**, for every objective
and preserved set. -/
theorem not_satisfiable_iff_exists_checkRed_unsat {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} :
    (¬ ∃ σ, ∀ c ∈ F, c.Holds σ) ↔
      ∃ (P : RedProof) (q : ℕ), P.conclusion = .unsat q ∧ checkRed F obj P pres = true := by
  refine ⟨fun h => ⟨_, _, rfl, checkRed_refutation_unsat (vs := F.flatMap PBConstr.vars) obj pres
      (fun c hc _ hx => List.mem_flatMap.2 ⟨c, hc, hx⟩) h⟩,
    fun ⟨P, q, hc, hP⟩ ⟨σ, hσ⟩ => not_satisfiable_of_checkRed hP hc σ hσ⟩

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

/-- After `soli` logs the full assignment of an optimal solution `σ`, adding the improving
constraint `f ≤ v - 1` for its value `v`, the state is refutable, with the conclusion
`BOUNDS v : q v`. -/
private theorem refutable_soli {F : List PBConstr} {f : Objective} {σ : ℕ → Bool}
    {vs : List ℕ} (pres : Option (List ℕ)) (hvs : ∀ c ∈ F, c.vars ⊆ vs)
    (hf : ∀ e ∈ f.lin, e.1 ∈ vs) (hσ : ∀ c ∈ F, c.Holds σ)
    (hopt : ∀ τ, (∀ c ∈ F, c.Holds τ) → f.eval σ ≤ f.eval τ) :
    Refutable F (some f) pres vs [.soli (solutionOf vs σ)]
      (fun q => .bounds (some (f.eval σ)) q (some (f.eval σ)) none)
      (((State.init F (some f) pres).log F (some f) (solutionOf vs σ)).improve f
        (f.eval (assignOf (solutionOf vs σ)))) := by
  set ρ := solutionOf vs σ
  set s₀ := State.init F (some f) pres
  set s₁ := (s₀.log F (some f) ρ).improve f (f.eval (assignOf ρ))
  have hval : f.eval (assignOf ρ) = f.eval σ := eval_assignOf_solutionOf hf
  have hstep : stepTop F (some f) s₀ (.soli ρ) = some s₁ := by
    have ha : assigns ρ f = true := assignsAll_solutionOf (List.forall_mem_map.2 hf)
    simpa [stepTop, s₁, s₀, State.init, map_snd_initDb, ha] using solves_initDb hvs hσ
  refine ⟨by rw [runTop_cons, hstep, Option.bind_some, runTop_nil], (idOk_initDb F).cons le_rfl _,
    fun e he x hx => ?_, fun ⟨τ, hτ⟩ => ?_, fun _ _ q hq => ?_⟩
  · rcases List.mem_cons.1 he with rfl | he
    · have := mem_vars_fromLinear (mem_vars_of_mem_vars_normalize hx)
      simp only [List.map_map, List.mem_map, Function.comp_apply] at this
      obtain ⟨e, he, rfl⟩ := this
      exact hf e he
    · exact vars_initDb hvs e he hx
  · have himp := (holds_normalize τ _).1 (hτ _ (List.mem_cons_self ..))
    rw [Objective.holds_improving, hval] at himp
    exact absurd (hopt τ (holds_of_allHold_initDb fun e he =>
      hτ e (List.mem_cons_of_mem _ he))) (not_le.2 himp)
  · simp [checkConclusion, s₁, s₀, State.improve, State.addCore, State.log, State.init, lowerTo,
      objValue, boundsOk, hq, hval]

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
        .bounds (some (f.eval σ)) q (some (f.eval σ)) none⟩ pres = true :=
  (refutable_soli pres hvs hf hσ hopt).exists_checkRed

/-- **The decision-tree proof of `BOUNDS v : q v`** for the solution `σ` of `F`, of value `v` under
the objective `f`, over the variables `vs`: `soli` logs the full assignment of `σ` to `vs`, adding
the improving constraint `f ≤ v - 1` as `|F| + 1`, and the decision tree over `vs` refutes the
database. -/
@[expose]
def boundsProof (F : List PBConstr) (f : Objective) (vs : List ℕ) (σ : ℕ → Bool) : RedProof :=
  ⟨.soli (solutionOf vs σ) :: (refuteSteps ((F.length + 1, (f.improving (f.eval σ)).normalize) ::
      initDb F) (F.length + 2) vs).map .step,
    .bounds (some (f.eval σ)) (F.length + 2 + (2 ^ (vs.length + 1) - 1) - 1) (some (f.eval σ))
      none⟩

/-- **The decision-tree proof of `BOUNDS v : q v` is accepted** for an optimal solution `σ`, of
value `v`, and a list `vs` containing the variables of `F` and of `f`, for every preserved set. -/
theorem checkRed_boundsProof {F : List PBConstr} {f : Objective} {σ : ℕ → Bool}
    {vs : List ℕ} (pres : Option (List ℕ)) (hvs : ∀ c ∈ F, c.vars ⊆ vs)
    (hf : ∀ e ∈ f.lin, e.1 ∈ vs) (hσ : ∀ c ∈ F, c.Holds σ)
    (hopt : ∀ τ, (∀ c ∈ F, c.Holds τ) → f.eval σ ≤ f.eval τ) :
    checkRed F (some f) (boundsProof F f vs σ) pres = true := by
  have h := (refutable_soli pres hvs hf hσ hopt).checkRed_refuteSteps
  simpa [boundsProof, State.improve, State.addCore, State.log, State.init,
    eval_assignOf_solutionOf hf,
    Nat.add_assoc] using h

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
  simpa using (refutable_init (obj := some f) (pres := pres) (vs := F.flatMap PBConstr.vars)
    (fun c hc _ hx => List.mem_flatMap.2 ⟨c, hc, hx⟩) h (c := fun q => .bounds none q none none)
    fun _ _ _ hq => by simp [checkConclusion, State.init, boundsOk, hq]).exists_checkRed

/-- **The decision-tree refutation proves `BOUNDS INF : q INF`** of an unsatisfiable formula over
the variables `vs`, for every objective and preserved set. -/
theorem checkRed_refutation_boundsInf {F : List PBConstr} {vs : List ℕ} (f : Objective)
    (pres : Option (List ℕ)) (hvs : ∀ c ∈ F, c.vars ⊆ vs) (h : ¬ ∃ σ, ∀ c ∈ F, c.Holds σ) :
    checkRed F (some f) (refutation F vs fun q => .bounds none q none none) pres = true := by
  simpa [State.init, refutation] using (refutable_init (obj := some f) (pres := pres) hvs h
    (c := fun q => .bounds none q none none)
    fun _ _ _ hq => by simp [checkConclusion, State.init, boundsOk, hq]).checkRed_refuteSteps

/-- **A formula is unsatisfiable iff the checker accepts a proof of `BOUNDS INF : q INF`**, for
every objective and preserved set. -/
theorem not_satisfiable_iff_exists_checkRed_boundsInf {F : List PBConstr} {f : Objective}
    {pres : Option (List ℕ)} :
    (¬ ∃ σ, ∀ c ∈ F, c.Holds σ) ↔
      ∃ (P : RedProof) (q : ℕ), P.conclusion = .bounds none q none none ∧
        checkRed F (some f) P pres = true := by
  refine ⟨fun h => ⟨_, _, rfl, checkRed_refutation_boundsInf (vs := F.flatMap PBConstr.vars) f
      pres (fun c hc _ hx => List.mem_flatMap.2 ⟨c, hc, hx⟩) h⟩,
    fun ⟨_, _, hc, hP⟩ ⟨σ, hσ⟩ => not_satisfiable_of_checkRed_bounds hP hc σ hσ⟩

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

/-- After `solx` logs the full assignments of solutions with distinct projections, which are all
the projections of solutions, the state is refutable, with the conclusion
`ENUMERATION_COMPLETE n : q` for the number `n` of solutions logged. -/
private theorem exists_refutable_solx {F : List PBConstr} {Pres vs : List ℕ}
    {σs : List (ℕ → Bool)} (hvs : ∀ c ∈ F, c.vars ⊆ vs)
    (hP : ∀ x ∈ Pres, x ∈ vs) (hσs : ∀ σ ∈ σs, ∀ c ∈ F, c.Holds σ)
    (hnd : (σs.map (proj Pres)).Nodup) (hall : ∀ l ∈ projections F Pres, l ∈ σs.map (proj Pres)) :
    ∃ s, Refutable F none (some Pres) vs (σs.map fun σ => .solx (solutionOf vs σ))
      (.enumComplete σs.length) s := by
  set s₀ := State.init F none (some Pres)
  have hs₀ : SolxReady Pres vs s₀ :=
    { pres := rfl, obj := rfl, chk := rfl, presChanged := rfl, idOk := idOk_initDb F
      vars := vars_initDb hvs }
  obtain ⟨s', hrun, hs', hlen, hexcl⟩ := exists_runTop_solx (F := F) hP σs s₀ hs₀
    (fun σ hσ => allHold_initDb (hσs σ hσ)) hnd
  refine ⟨s', hrun, hs'.idOk, hs'.vars, fun ⟨τ, hτ⟩ => ?_, fun _ _ q hq => ?_⟩
  · obtain ⟨hτ₀, hτσs⟩ := hexcl τ hτ
    obtain ⟨σ, hσ, he⟩ := List.mem_map.1 (hall _ ⟨τ, holds_of_allHold_initDb hτ₀, rfl⟩)
    exact hτσs σ hσ he.symm
  · simp [checkConclusion, hs'.pres, hlen, s₀, State.init, hq]

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
        .enumComplete σs.length q⟩ (some Pres) = true :=
  (exists_refutable_solx hvs hP hσs hnd hall).choose_spec.exists_checkRed

/-- **The decision-tree proof of `ENUMERATION_COMPLETE n : q`** for the solutions `σs` of `F`, over
the variables `vs`, with the preserved set `Pres`: `solx` logs the full assignment of each to `vs`,
and the decision tree over `vs` refutes the database that the `solx` steps reach. -/
@[expose]
def enumProof (F : List PBConstr) (Pres vs : List ℕ) (σs : List (ℕ → Bool)) : RedProof :=
  let pre : List TopStep := σs.map fun σ => .solx (solutionOf vs σ)
  match runTop F none (State.init F none (some Pres)) pre with
  | some s => ⟨pre ++ (refuteSteps s.db s.next vs).map .step,
      .enumComplete σs.length (s.next + (2 ^ (vs.length + 1) - 1) - 1)⟩
  | none => ⟨pre, .noClaim⟩

/-- **The decision-tree proof of `ENUMERATION_COMPLETE n : q` is accepted** for solutions `σs` of
`F` whose projections to `Pres` are distinct and are all the projections of solutions, and a list
`vs` containing the variables of `F` and of `Pres`. -/
theorem checkRed_enumProof {F : List PBConstr} {Pres vs : List ℕ}
    {σs : List (ℕ → Bool)} (hvs : ∀ c ∈ F, c.vars ⊆ vs)
    (hP : ∀ x ∈ Pres, x ∈ vs) (hσs : ∀ σ ∈ σs, ∀ c ∈ F, c.Holds σ)
    (hnd : (σs.map (proj Pres)).Nodup) (hall : ∀ l ∈ projections F Pres, l ∈ σs.map (proj Pres)) :
    checkRed F none (enumProof F Pres vs σs) (some Pres) = true ∧
      ∃ q, (enumProof F Pres vs σs).conclusion = .enumComplete σs.length q := by
  obtain ⟨s, hs⟩ := exists_refutable_solx hvs hP hσs hnd hall
  simp only [enumProof, hs.run]
  exact ⟨hs.checkRed_refuteSteps, _, rfl⟩

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

/-! ### The producers -/

/-- **All assignments of the variables `vs`**, false on every other variable: `2 ^ |vs|` of them,
one per assignment of `vs` if its variables are distinct. -/
@[expose]
def assignments : List ℕ → List (ℕ → Bool)
  | [] => [fun _ => false]
  | x :: xs =>
    (assignments xs).flatMap fun σ => [Function.update σ x true, Function.update σ x false]

theorem length_assignments : ∀ vs : List ℕ, (assignments vs).length = 2 ^ vs.length
  | [] => rfl
  | x :: xs => by
    rw [assignments, List.length_flatMap]
    simp [length_assignments xs, pow_succ, Nat.mul_comm]

/-- Every assignment agrees on `vs` with one of the assignments of `vs`. -/
theorem exists_mem_assignments (σ : ℕ → Bool) :
    ∀ vs : List ℕ, ∃ τ ∈ assignments vs, ∀ x ∈ vs, τ x = σ x
  | [] => ⟨_, List.mem_singleton_self _, by simp⟩
  | x :: xs => by
    obtain ⟨τ, hτ, hag⟩ := exists_mem_assignments σ xs
    refine ⟨Function.update τ x (σ x), List.mem_flatMap.2 ⟨τ, hτ, ?_⟩, fun y hy => ?_⟩
    · cases σ x <;> simp
    · by_cases hyx : y = x
      · subst hyx; simp
      · rw [Function.update_of_ne hyx]
        exact hag y ((List.mem_cons.1 hy).resolve_left hyx)

/-- **The solutions of `F` among the assignments of `vs`.** -/
@[expose]
def solutionsOn (F : List PBConstr) (vs : List ℕ) : List (ℕ → Bool) :=
  (assignments vs).filter fun σ => F.all fun c => decide (c.Holds σ)

theorem holds_of_mem_solutionsOn {F : List PBConstr} {vs : List ℕ} {σ : ℕ → Bool}
    (h : σ ∈ solutionsOn F vs) : ∀ c ∈ F, c.Holds σ := by
  simpa [solutionsOn] using (List.mem_filter.1 h).2

/-- Every solution of `F` agrees on `vs`, which contains the variables of `F`, with one of
`solutionsOn F vs`. -/
theorem exists_mem_solutionsOn {F : List PBConstr} {vs : List ℕ} (hvs : ∀ c ∈ F, c.vars ⊆ vs)
    {σ : ℕ → Bool} (hσ : ∀ c ∈ F, c.Holds σ) :
    ∃ τ ∈ solutionsOn F vs, ∀ x ∈ vs, τ x = σ x := by
  obtain ⟨τ, hτ, hag⟩ := exists_mem_assignments σ vs
  refine ⟨τ, List.mem_filter.2 ⟨hτ, ?_⟩, hag⟩
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact fun c hc => (holds_congr fun t ht =>
    hag _ (hvs c hc (List.mem_map_of_mem ht))).2 (hσ c hc)

private theorem solutionsOn_eq_nil_iff {F : List PBConstr} {vs : List ℕ}
    (hvs : ∀ c ∈ F, c.vars ⊆ vs) : solutionsOn F vs = [] ↔ ¬ ∃ σ, ∀ c ∈ F, c.Holds σ := by
  refine ⟨fun h ⟨σ, hσ⟩ => ?_, fun h => List.eq_nil_iff_forall_not_mem.2 fun σ hσ =>
    h ⟨σ, holds_of_mem_solutionsOn hσ⟩⟩
  obtain ⟨τ, hτ, -⟩ := exists_mem_solutionsOn hvs hσ
  simp [h] at hτ

private theorem vars_subset_dedup {F : List PBConstr} {L : List ℕ}
    (hL : F.flatMap PBConstr.vars ⊆ L) : ∀ c ∈ F, c.vars ⊆ L.dedup :=
  fun c hc _ hx => List.mem_dedup.2 (hL (List.mem_flatMap.2 ⟨c, hc, hx⟩))

/-- **The `UNSAT` producer**: the decision-tree refutation of `F` over its distinct variables, if
`F` has no solution, found by trying every assignment of them. -/
@[expose]
def refute (F : List PBConstr) : Option RedProof :=
  if solutionsOn F (F.flatMap PBConstr.vars).dedup = [] then
    some (refutation F (F.flatMap PBConstr.vars).dedup .unsat)
  else none

/-- `refute F` returns a proof exactly when `F` has no solution. -/
theorem isSome_refute {F : List PBConstr} : (refute F).isSome ↔ ¬ ∃ σ, ∀ c ∈ F, c.Holds σ := by
  rw [← solutionsOn_eq_nil_iff (vars_subset_dedup (List.Subset.refl _))]
  unfold refute
  split_ifs with h <;> simp [h]

/-- **The proof of `refute` is accepted**, for every objective and preserved set, with conclusion
`UNSAT`, and it has `2 ^ (k + 1) - 1` steps for the number `k` of distinct variables of `F`, each a
`rup` step of a clause of at most `k` literals with at most three hints
(`Cslib.Logic.PL.VeriPB.exists_eq_rup_of_mem_refuteSteps`). -/
theorem checkRed_of_refute_eq_some {F : List PBConstr} {P : RedProof} (h : refute F = some P)
    (obj : Option Objective) (pres : Option (List ℕ)) :
    checkRed F obj P pres = true ∧ (∃ q, P.conclusion = .unsat q) ∧
      P.steps.length = 2 ^ ((F.flatMap PBConstr.vars).dedup.length + 1) - 1 := by
  unfold refute at h
  split_ifs at h with hs
  cases h
  refine ⟨checkRed_refutation_unsat obj pres (vars_subset_dedup (List.Subset.refl _))
    ((solutionsOn_eq_nil_iff (vars_subset_dedup (List.Subset.refl _))).1 hs), ⟨_, rfl⟩, ?_⟩
  simp [refutation, length_refuteSteps]

/-- **The `SAT` producer**: the empty proof with the full assignment of the first solution of `F`
among the assignments of its distinct variables, if there is one. -/
@[expose]
def solve (F : List PBConstr) : Option RedProof :=
  (solutionsOn F (F.flatMap PBConstr.vars).dedup).head?.map fun σ =>
    ⟨[], .sat (some (solutionOf (F.flatMap PBConstr.vars).dedup σ))⟩

/-- `solve F` returns a proof exactly when `F` has a solution. -/
theorem isSome_solve {F : List PBConstr} : (solve F).isSome ↔ ∃ σ, ∀ c ∈ F, c.Holds σ := by
  rw [← not_iff_not, ← solutionsOn_eq_nil_iff (vars_subset_dedup (List.Subset.refl _))]
  simp [solve]

/-- **The proof of `solve` is accepted**, for every objective and preserved set, with conclusion
`SAT : ρ`. -/
theorem checkRed_of_solve_eq_some {F : List PBConstr} {P : RedProof} (h : solve F = some P)
    (obj : Option Objective) (pres : Option (List ℕ)) :
    checkRed F obj P pres = true ∧ ∃ ρ, P.conclusion = .sat (some ρ) := by
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨checkRed_sat_solutionOf obj pres (vars_subset_dedup (List.Subset.refl _))
    (holds_of_mem_solutionsOn (List.mem_of_mem_head? hσ)), _, rfl⟩

/-- **The `BOUNDS` producer** for the objective `f`: over the distinct variables `vs` of `F` and
`f`, the decision-tree proof of `BOUNDS v : q v` for a solution of least value `v` among the
assignments of `vs`, and the decision-tree refutation with `BOUNDS INF : q INF` if there is
none. -/
@[expose]
def optimize (F : List PBConstr) (f : Objective) : RedProof :=
  match (solutionsOn F (F.flatMap PBConstr.vars ++ f.lin.map (·.1)).dedup).argmin f.eval with
  | some σ => boundsProof F f (F.flatMap PBConstr.vars ++ f.lin.map (·.1)).dedup σ
  | none => refutation F (F.flatMap PBConstr.vars ++ f.lin.map (·.1)).dedup
      fun q => .bounds none q none none

/-- **The proof of `optimize` is accepted**, for every preserved set, with conclusion
`BOUNDS lb : q lb`: for a finite `lb` the optimum is `lb`
(`Cslib.Logic.PL.VeriPB.isLeast_iff_exists_checkRed_bounds`), and `INF` means that `F` has no
solution (`Cslib.Logic.PL.VeriPB.not_satisfiable_iff_exists_checkRed_boundsInf`). -/
theorem checkRed_optimize (F : List PBConstr) (f : Objective) (pres : Option (List ℕ)) :
    checkRed F (some f) (optimize F f) pres = true ∧
      ∃ lb q, (optimize F f).conclusion = .bounds lb q lb none := by
  set vs := (F.flatMap PBConstr.vars ++ f.lin.map (·.1)).dedup
  have hf : ∀ e ∈ f.lin, e.1 ∈ vs :=
    fun e he => List.mem_dedup.2 (List.mem_append_right _ (List.mem_map_of_mem he))
  have hF : ∀ c ∈ F, c.vars ⊆ vs := vars_subset_dedup (List.subset_append_left _ _)
  unfold optimize
  rcases hm : (solutionsOn F vs).argmin f.eval with _ | σ
  · exact ⟨checkRed_refutation_boundsInf f pres hF
      ((solutionsOn_eq_nil_iff hF).1 (List.argmin_eq_none.1 hm)), none, _, rfl⟩
  · refine ⟨checkRed_boundsProof pres hF hf
      (holds_of_mem_solutionsOn (List.argmin_mem hm)) fun τ hτ => ?_, _, _, rfl⟩
    obtain ⟨τ', hτ', hag⟩ := exists_mem_solutionsOn hF hτ
    rw [← show f.eval τ' = f.eval τ by
      rw [Objective.eval, Objective.eval, linVal_congr fun e he => hag _ (hf e he)]]
    exact List.le_of_mem_argmin hτ' hm

/-- **The `ENUMERATION_COMPLETE` producer** for the preserved set `Pres`: over the distinct
variables `vs` of `F` and `Pres`, the decision-tree proof of `ENUMERATION_COMPLETE n : q` for the
first solution of each projection among the assignments of `vs`. -/
@[expose]
def enumerate (F : List PBConstr) (Pres : List ℕ) : RedProof :=
  enumProof F Pres (F.flatMap PBConstr.vars ++ Pres).dedup
    ((solutionsOn F (F.flatMap PBConstr.vars ++ Pres).dedup).pwFilter
      fun σ τ => proj Pres σ ≠ proj Pres τ)

/-- **The proof of `enumerate` is accepted** with the preserved set `Pres` and no objective, with
conclusion `ENUMERATION_COMPLETE n : q`, where `n` is the number of projections of solutions to
`Pres` (`Cslib.Logic.PL.VeriPB.encard_eq_of_checkRed_enumComplete`). -/
theorem checkRed_enumerate (F : List PBConstr) (Pres : List ℕ) :
    checkRed F none (enumerate F Pres) (some Pres) = true ∧
      ∃ n q, (enumerate F Pres).conclusion = .enumComplete n q := by
  set vs := (F.flatMap PBConstr.vars ++ Pres).dedup
  set σs := (solutionsOn F vs).pwFilter fun σ τ => proj Pres σ ≠ proj Pres τ
  have hP : ∀ x ∈ Pres, x ∈ vs := fun x hx => List.mem_dedup.2 (List.mem_append_right _ hx)
  have hsub : ∀ σ ∈ σs, σ ∈ solutionsOn F vs := fun σ hσ => List.pwFilter_subset _ hσ
  have hF : ∀ c ∈ F, c.vars ⊆ vs := vars_subset_dedup (List.subset_append_left _ _)
  have hall : ∀ l ∈ projections F Pres, l ∈ σs.map (proj Pres) := fun l ⟨τ, hτ, hl⟩ => by
    obtain ⟨τ', hτ', hag⟩ := exists_mem_solutionsOn hF hτ
    have hl' : proj Pres τ' = l := hl ▸ proj_eq_iff.2 fun v hv => hag v (hP v hv)
    by_contra hne
    have := (List.forall_mem_pwFilter (R := fun σ τ => proj Pres σ ≠ proj Pres τ)
      (fun {x y z} h => by by_cases hxy : proj Pres x = proj Pres y <;> simp_all) τ'
      (solutionsOn F vs)).1 fun b hb hb' => hne (List.mem_map.2 ⟨b, hb, hb'.symm.trans hl'⟩)
    exact this τ' hτ' rfl
  obtain ⟨hP', q, hq⟩ := checkRed_enumProof hF hP (fun σ hσ => holds_of_mem_solutionsOn (hsub σ hσ))
    (List.pairwise_map.2 (List.pairwise_pwFilter _)) hall
  exact ⟨hP', _, q, hq⟩

end VeriPB

end Cslib.Logic.PL
