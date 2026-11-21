/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.VeriPB
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A VeriPB kernel-proof checker: redundance, objectives, solution logging and conclusions

The rule `red C : ω` of VeriPB [Bogaerts, Gocht, McCreesh and
Nordström][BogaertsGochtMcCreeshNordstrom2023] adds a constraint `C` that need not follow from
the database, justified by a *witness* `ω`: a substitution of variables by `0`, `1` or literals
(`Cslib.Logic.PL.VeriPB.Witness`). Applying `ω` to a constraint `D` gives `D|ω`
(`Cslib.Logic.PL.VeriPB.Witness.substC`), and `σ` satisfies `D|ω` exactly when `σ ∘ ω`
(`Cslib.Logic.PL.VeriPB.Witness.apply`) satisfies `D`
(`Cslib.Logic.PL.VeriPB.Witness.holds_substC`). Citations of sections below are to the
VeriPB/CakePB documentation, 22 June 2026 edition.

**Objectives.** An optimization problem minimizes an objective `f = ∑ wᵥ xᵥ + k` with integer
weights (§3.2; `Cslib.Logic.PL.VeriPB.Objective`); a decision problem has the trivial objective
`0` (§5, `Cslib.Logic.PL.VeriPB.objValue`). The rule `red` must then preserve an *optimal*
solution, not only a solution (§5.4.1, equation (5.3)): every assignment `σ` satisfying the
database and violating `C` must be repaired by `ω`, so that `σ ∘ ω` satisfies the database and
`C`, *and does not increase the objective*, `f|ω ≤ f`. The *proof goals* are `C|ω` (label `#1`),
`D|ω` for every constraint `D` of the database, and `f|ω ≤ f`
(`Cslib.Logic.PL.VeriPB.objGoal`; label `#2`, as there is no order), each to be shown from the
database and `¬C`.

**The step** (`Cslib.Logic.PL.VeriPB.redCheck`), as in VeriPB and CakePB: `¬C` takes the next
number and the subproof runs. Its items are derivation steps (`Cslib.Logic.PL.VeriPB.Step`,
including deletion), which may use `¬C`, and `proofgoal` blocks
(`Cslib.Logic.PL.VeriPB.RedItem.goal`), each starting from the negation of its goal and ending at
a contradiction, after which its constraints are dropped; a block is checked by
`Cslib.Logic.PL.VeriPB.subproofRefutes`, as a `pbc` subproof is. The step is
accepted when the subproof closes with a contradiction (then `C` follows outright), or when every
goal is covered (`Cslib.Logic.PL.VeriPB.goalCovered`), following the autoproven goals of the
kernel format (§5.5.1): trivially true after normalization, in the database up to the order of
terms, proved by a `proofgoal` block, or weakly syntactically implied by `¬C`
(`Cslib.Logic.PL.VeriPB.weakImplies`). A database goal `D|ω` is also covered when `ω` sets every
literal of `D` it touches true, or when `D` weakly syntactically implies it. `C` takes the number
after the subproof, whose constraints are dropped. The premise `f ≤ v - 1` of (5.3), for the best
value `v` logged so far, is not added: it is not needed for soundness, and a proof can use the
objective-improving constraint in the database instead.

**Weak syntactic implication.** The test is that, in the linear forms `∑ dᵥ xᵥ ≥ A` of `D` and
`∑ cᵥ xᵥ ≥ B` of `C`, `B + ∑ᵥ max(0, dᵥ - cᵥ) ≤ A`. It bounds the slack of `C` below by that of
`D` on every assignment (`Cslib.Logic.PL.VeriPB.Holds.of_weakImplies`), and it covers a `C`
obtained from `D` by adding literal axioms.

**Solution logging** (§5.8). `sol ρ` and `soli ρ` log a solution `ρ`, a list of literals
(`Cslib.Logic.PL.VeriPB.TopStep`). As in the kernel format (§6.1), `ρ` is not propagated: its
literals must be consistent and must satisfy every constraint of the database on their own
(`Cslib.Logic.PL.VeriPB.solves`), so that every assignment extending `ρ` is a solution; the
values below are taken at the extension `Cslib.Logic.PL.VeriPB.assignOf` setting every other
variable false. `soli ρ` also needs an objective that `ρ` assigns completely, and adds the
objective-improving constraint `f ≤ f(ρ) - 1` (equation (3.6);
`Cslib.Logic.PL.VeriPB.Objective.improving`). `obji v` adds the improving constraint `f ≤ v - 1`
without a solution (§5.8.2).

**Objective updates** (§5.9). `obju new g` replaces the current objective `f` by `g`, and
`obju diff g` by `f + g` (`Cslib.Logic.PL.VeriPB.objuCheck`), whose weights are merged per
variable and whose zero weights are dropped (`Cslib.Logic.PL.VeriPB.Objective.add`), so that
`soli` need not assign a variable the update cancels. Its goals are `#1`, the
constraint `f' ≥ f` for the new objective `f'`, and `#2`, `f ≥ f'`. Both must follow from the
core set alone: each is trivially true, a constraint of the core up to the order of terms, or
proved by a `proofgoal` block run on the core. So the two objectives agree on every solution of
the core (`Cslib.Logic.PL.VeriPB.objuCheck_sound`). The state carries the current objective,
which the rules after the update use. Values logged earlier are kept as numbers, as CakePB keeps
`bound` and `dbound`: a solution's value under a later objective could differ.

**Projected enumeration** (§5.8.3, §4.3). An input may name a *preserved set* `P` of
variables. `solx ρ` logs a solution `ρ` of the database that assigns every variable of `P`, and
adds to the core its *solution-excluding constraint*, which holds exactly at the assignments
whose projection to `P` differs from that of `ρ` (`Cslib.Logic.PL.VeriPB.exclusion`). As in
CakePB, `solx` needs no objective and no earlier unchecked deletion, and the witnesses of `red`
and of checked deletion must leave the variables of `P` alone (`Cslib.Logic.PL.VeriPB.presFree`,
CakePB's `check_pres`). `ENUMERATION_PARTIAL n` claims `n` distinct projections of solutions;
`ENUMERATION_COMPLETE n : q` claims exactly `n`, with the contradiction `q`. Both need a
preserved set, even for `n = 0`: VeriPB 3.0.2 and CakePB accept `ENUMERATION_* 0` without a
`preserved:` line, and this checker rejects it. A variable listed twice in the preserved set
counts once. The rules that change the preserved set (`preserved_add`, `preserved_rm`, §5.10) are
not supported.

**Core and derived constraints** (§3.4). The database is split into a *core set* and a *derived
set* (`Cslib.Logic.PL.VeriPB.State`). The input constraints start in the core. Implicational
steps and `red` add derived constraints. `soli` adds its improving constraint to the core, and
`core id` moves constraints there; promoting a core constraint again is a no-op (§5.1, as
CakePB's `do_transfer`). Deletion is typed (§5.7.1):
* `deld` deletes derived constraints only.
* `delc` deletes core constraints without a check. Such an *unchecked deletion* clears the flag
  `chk`.
* The checked deletion `delc id : ω` must show that the deleted constraint `C` is redundant with
  respect to the remaining core set alone. It is the redundance check
  (`Cslib.Logic.PL.VeriPB.redCheckOn`) with premises and goals taken from the core without `C`,
  as in CakePB (`CheckedDelete` in `check_cstep`).

In *strengthening-to-core mode* (§5.6), switched on by `strengthening_to_core on`, which moves
every constraint to the core, `red` adds core constraints, and its goals cover only the core set
and not the derived set. In this mode a checked deletion is a proof by contradiction: it takes no
witness and its subproof must end in a contradiction `qed : n`, as CakePB requires
(`check_tcb_idopt`); VeriPB 3.0.2 also accepts a subproof without it. An unchecked core deletion
needs an empty derived set (§5.7.4). The untyped deletion `del id` of the augmented format
(`Cslib.Logic.PL.VeriPB.Step.del`, §5.7.2) is unchecked when it deletes a core constraint, and this
checker rejects such a deletion in strengthening-to-core mode.

**Solutions and conclusions.** The checker keeps a bound and a logged solution, as CakePB keeps
`dbound` and `bound` (`update_dbound`, `update_bound` and `check_hconcl` in
`npbc_checkScript.sml`).
* The bound `dbound` is the least value of a logged solution or of an `obji` step. The lower
  bounds are checked against it. As `obji` asserts its value without a solution, `dbound` need
  not be the value of any solution.
* The bound `bound` certifies `SAT` and finite upper bounds. It is the least value of a solution
  logged while `chk` held, as in VeriPB and CakePB, at its value under the objective of that time,
  or of one that solves the input formula, which this checker tests when the solution is logged,
  at its value under the input objective (`Cslib.Logic.PL.VeriPB.State.log`). Any other logged
  solution leaves `bound` unchanged.

The conclusions (§4.3; `Cslib.Logic.PL.VeriPB.Conclusion`):
* `UNSAT : q` needs a contradiction `q`, no logged solution and no `obji` step.
* `SAT` needs `bound` set. `SAT : ρ` instead needs the stated assignment `ρ` to solve the input
  formula, whatever was logged.
* `BOUNDS lb : q ub` needs an objective. The lower bound `lb` must be at most `dbound`, and `q`
  must be a contradiction or weakly syntactically imply `f ≥ lb` for the final objective `f`;
  `lb = INF` is checked as `UNSAT`. The upper bound `ub`, unless `INF`, must be `bound`; with an
  assignment `BOUNDS lb : q ub : ρ`, `ρ` must instead solve the input formula, assign every
  objective variable and have value `ub` under the input objective, as in VeriPB. As in VeriPB,
  an assignment after an infinite upper bound is not checked.
* `NONE` claims nothing; the proof is still checked step by step.

§4.3 gives `BOUNDS` for optimization problems; accepting `UNSAT` and `SAT` under an objective as
well is an extension of this checker.

**The invariants.** Each step keeps the invariants below (`Cslib.Logic.PL.VeriPB.stepTop_inv`,
`Cslib.Logic.PL.VeriPB.stepTop_reachesOn`, `Cslib.Logic.PL.VeriPB.stepTop_enumInv`,
`Cslib.Logic.PL.VeriPB.stepTop_covers`), as CakePB's `check_csteps_correct` does (CakeML
commit `14856fcf`); they hold after every run (`Cslib.Logic.PL.VeriPB.invariants_of_runTop`).
* *The core invariant* (`Cslib.Logic.PL.VeriPB.Inv`). The core set lies in the database. In
  strengthening-to-core mode, the core set implies the database, which justifies the smaller
  goal set of `red` there; this is `valid_conf` of CakePB. While `chk` holds, every solution of
  the core set gives a solution of the input formula with no larger objective value and the same
  projection to the preserved set. Adding core constraints only shrinks the solutions of the
  core. A checked deletion of `C` repairs a solution of the remaining core into one of the whole
  core without raising the objective, with a witness that leaves the preserved set alone, and
  `obju` keeps the objective's values on the core. So `bound` is at least the input value of
  some input solution.
* *The lower-bound invariant* (`Cslib.Logic.PL.VeriPB.ReachesOn`). For a value `w` and an
  assignment `σ₀`, either some solution of the database that agrees with `σ₀` on the preserved
  set has objective at most `w`, or `dbound` is at most `w`
  (`Cslib.Logic.PL.VeriPB.Reaches` forgets the projection).
  * An implicational step keeps every solution, and a deletion enlarges the set of solutions.
  * A `red` step repairs a solution without raising the objective or moving a preserved
    variable. In strengthening-to-core mode, the repaired solution satisfies the core, hence the
    database.
  * `soli ρ` removes only solutions of objective at least `f(ρ)`, and lowers `dbound` to `f(ρ)`;
    `obji v` removes only solutions of objective at least `v`, and lowers `dbound` to `v`.

  Every solution `σ` of the formula meets this invariant initially for `w = f(σ)` and `σ₀ = σ`,
  which gives the lower bounds. It is CakePB's invariant `bimp_obj`.

  These two invariants are CakePB's `bimp_pres_obj`. For each bound `v` on the objective,
  `bimp_pres_obj` gives injections between the projections to the preserved set of the solutions
  of value at most `v`: forward from the input to the database below `dbound`, and backward from
  the core set to the input while `chk` holds. Here the preserved set does not change and
  witnesses leave it alone, so both injections are the identity on projections, and the
  invariants state them as inclusions of projected solution sets. The backward inclusion holds
  for every `v`, not only below `bound` as in CakePB.
  The output sections (`CslibFrontier.Logics.Propositional.PseudoBoolean.Output`) rest on them.
* *The enumeration invariants*, the counting half of CakePB's `check_csteps_correct`.
  * Backward (`Cslib.Logic.PL.VeriPB.EnumInv`): the logged projections are distinct, and each is
    the projection of an input solution. While `chk` holds, no core solution has a logged
    projection. `solx` keeps this, because its exclusion constraint removes exactly the
    projection it logs.
  * Forward (`Cslib.Logic.PL.VeriPB.Covers`): without an objective, the projection of every input
    solution is that of a database solution, or has been logged. Witnesses keep projections, and
    an exclusion constraint removes only a logged projection.

  Together they give the count of `ENUMERATION` (`Cslib.Logic.PL.VeriPB.projections`).

The soundness theorems follow CakePB's semantics of conclusions (`sem_concl`, `npbcScript.sml`).
In particular a finite upper bound `ub` certifies a solution of value at most `ub`.

**Scope.** There is no order, so no dominance and no order goals. Neither the preserved-set rules
(§5.10) nor deletion by specification and levels (§5.7.2) are supported, nor `UNSAT` without a
constraint ID (the kernel format requires one). Matching VeriPB, `red` steps are not
cutting-planes steps, and the translation of `Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check`
covers only proofs without them.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Witness`, `Cslib.Logic.PL.VeriPB.Witness.substC`: witnesses and
  substitution.
* `Cslib.Logic.PL.VeriPB.Objective`, `Cslib.Logic.PL.VeriPB.objGoal`: objectives and the
  objective goal of `red`.
* `Cslib.Logic.PL.VeriPB.TopStep`, `Cslib.Logic.PL.VeriPB.Conclusion`,
  `Cslib.Logic.PL.VeriPB.RedProof`, `Cslib.Logic.PL.VeriPB.checkRed`: proofs with `red`,
  solution-logging, core and deletion steps, their conclusions, and their checker.
* `Cslib.Logic.PL.VeriPB.State`, `Cslib.Logic.PL.VeriPB.stepTop`: the checker state, with its
  core set, and one top-level step.
* `Cslib.Logic.PL.VeriPB.Objective.add`, `Cslib.Logic.PL.VeriPB.objuCheck`: the sum of
  objectives and the check of an objective update `obju`.
* `Cslib.Logic.PL.VeriPB.proj`, `Cslib.Logic.PL.VeriPB.exclusion`,
  `Cslib.Logic.PL.VeriPB.presFree`, `Cslib.Logic.PL.VeriPB.projections`: projections to the
  preserved set, the solution-excluding constraint of `solx`, witnesses that leave the preserved
  set alone, and the projected solutions that `ENUMERATION` counts.

## Main results

* `Cslib.Logic.PL.VeriPB.Witness.holds_substC`: `σ ⊨ D|ω` iff `σ ∘ ω ⊨ D`.
* `Cslib.Logic.PL.VeriPB.redCheck_sound`, `Cslib.Logic.PL.VeriPB.redCheckOn_sound`: a checked
  `red` step repairs a solution of the database without raising the objective.
* `Cslib.Logic.PL.VeriPB.objuCheck_sound`: a checked objective update keeps the objective's
  values on the solutions of the core set; `Cslib.Logic.PL.VeriPB.Objective.eval_add`: the value
  of a sum of objectives.
* `Cslib.Logic.PL.VeriPB.stepTop_inv`, `Cslib.Logic.PL.VeriPB.stepTop_reachesOn`,
  `Cslib.Logic.PL.VeriPB.stepTop_reaches`: the core and lower-bound invariants;
  `Cslib.Logic.PL.VeriPB.invariants_of_runTop`: all invariants after a run.
* `Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_cnf_of_checkRed`: soundness for `UNSAT`.
* `Cslib.Logic.PL.VeriPB.exists_satisfies_of_checkRed`: soundness for `SAT`.
* `Cslib.Logic.PL.VeriPB.le_eval_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed_bounds`,
  `Cslib.Logic.PL.VeriPB.exists_eval_le_of_checkRed`: soundness for `BOUNDS`, its lower bound,
  infinite lower bound and upper bound.
* `Cslib.Logic.PL.VeriPB.holds_exclusion`: the solution-excluding constraint holds exactly off the
  logged projection.
* `Cslib.Logic.PL.VeriPB.stepTop_enumInv`, `Cslib.Logic.PL.VeriPB.stepTop_covers`: the
  enumeration invariants.
* `Cslib.Logic.PL.VeriPB.isSome_of_checkRed_enum`,
  `Cslib.Logic.PL.VeriPB.le_encard_of_checkRed_enum`,
  `Cslib.Logic.PL.VeriPB.encard_eq_of_checkRed_enumComplete`: soundness for `ENUMERATION`.
* `Cslib.Logic.PL.VeriPB.checkRed_map_step`: without `red` and solutions, the checker of
  `Cslib.Logic.PL.VeriPB.check`.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace VeriPB

open PBConstr

/-! ### Witnesses -/

/-- The value a witness gives a variable. -/
inductive WVal where
  /-- The constant `0`. -/
  | zero
  /-- The constant `1`. -/
  | one
  /-- A literal. -/
  | lit (l : Literal ℕ)
  deriving DecidableEq, Repr

/-- A witness: a substitution of variables by `0`, `1` or literals, as a list of pairs; a
variable not listed is left alone. -/
abbrev Witness := List (ℕ × WVal)

namespace Witness

/-- The value the witness gives `v`, if any. -/
def find (ω : Witness) (v : ℕ) : Option WVal := (ω.find? (·.1 == v)).map (·.2)

/-- The assignment `σ ∘ ω`: the value of `v` under `ω`, evaluated in `σ`. -/
def apply (σ : ℕ → Bool) (ω : Witness) (v : ℕ) : Bool :=
  match ω.find v with
  | none => σ v
  | some .zero => false
  | some .one => true
  | some (.lit l) => Literal.eval σ l

/-- A term under the witness: the terms it becomes and the constant it contributes. -/
def substTerm (ω : Witness) (t : ℕ × Literal ℕ) : List (ℕ × Literal ℕ) × ℕ :=
  match ω.find (termVar t) with
  | none => ([t], 0)
  | some .zero => ([], if termPos t then 0 else t.1)
  | some .one => ([], if termPos t then t.1 else 0)
  | some (.lit l) => ([(t.1, if termPos t then l else Std.Sat.Literal.negate l)], 0)

/-- **The constraint `D|ω`**: every term under the witness, constants moved into the degree. -/
def substC (ω : Witness) (c : PBConstr) : PBConstr :=
  ⟨c.terms.flatMap fun t => (substTerm ω t).1,
    c.degree - (c.terms.map fun t => (substTerm ω t).2).sum⟩

theorem not_beq_eq_beq_not (x y : Bool) : (!x == y) = (x == !y) := by
  cases x <;> cases y <;> rfl

theorem termVal_apply (σ : ℕ → Bool) (ω : Witness) (t : ℕ × Literal ℕ) :
    termVal (apply σ ω) t = lhs σ (substTerm ω t).1 + (substTerm ω t).2 := by
  obtain ⟨a, v, b⟩ := t
  simp only [substTerm, termVar_mk, termPos_mk]
  unfold termVal apply
  simp only [Literal.eval]
  cases hf : ω.find v with
  | none => simp [termVal, Literal.eval]
  | some w =>
    cases w <;> cases b <;>
      simp [termVal, Literal.eval, Std.Sat.Literal.negate, not_beq_eq_beq_not]

theorem lhs_apply (σ : ℕ → Bool) (ω : Witness) (ts : List (ℕ × Literal ℕ)) :
    lhs (apply σ ω) ts = lhs σ (ts.flatMap fun t => (substTerm ω t).1) +
      (ts.map fun t => (substTerm ω t).2).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [lhs_cons, termVal_apply, ih, List.flatMap_cons, lhs_append, List.map_cons,
      List.sum_cons]
    omega

/-- **Substitution and composition**: `σ` satisfies `D|ω` exactly when `σ ∘ ω` satisfies `D`. -/
theorem holds_substC (σ : ℕ → Bool) (ω : Witness) (c : PBConstr) :
    (substC ω c).Holds σ ↔ c.Holds (apply σ ω) := by
  unfold Holds substC
  rw [lhs_apply]
  simp only
  omega

/-- Every literal of `c` that the witness touches is set true by it. -/
def touchedTrue (ω : Witness) (c : PBConstr) : Bool :=
  c.terms.all fun t =>
    match ω.find (termVar t) with
    | none => true
    | some .zero => !termPos t
    | some .one => termPos t
    | some (.lit _) => false

/-- If the witness sets every literal it touches true, it can only raise the left-hand side. -/
theorem Holds.apply_of_touchedTrue {σ : ℕ → Bool} {ω : Witness} {c : PBConstr}
    (h : touchedTrue ω c = true) (hc : c.Holds σ) : c.Holds (apply σ ω) := by
  unfold Holds at hc ⊢
  refine hc.trans ?_
  unfold touchedTrue at h
  rw [List.all_eq_true] at h
  generalize c.terms = ts at h ⊢
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [lhs_cons]
    have ht := h t (by simp)
    have := ih fun t' h' => h t' (by simp [h'])
    suffices termVal σ t ≤ termVal (apply σ ω) t by omega
    obtain ⟨a, v, b⟩ := t
    simp only [termVar_mk, termPos_mk] at ht
    unfold termVal apply
    simp only [Literal.eval]
    cases hf : ω.find v with
    | none => simp
    | some w =>
      simp only [hf] at ht
      cases w <;> cases b <;> simp_all <;> cases σ v <;> simp

end Witness

/-! ### Objectives -/

/-- An objective `∑ᵥ wᵥ xᵥ + k` to minimize (§3.2 of the VeriPB/CakePB documentation, 22 June
2026 edition), as an integer linear form over variables and a constant. A negative literal
`w ¬x` is `w - w x`. -/
structure Objective where
  /-- The weights `wᵥ`. -/
  lin : List (ℕ × ℤ)
  /-- The constant `k`. -/
  const : ℤ
  deriving DecidableEq, Repr

namespace Objective

/-- The value of the objective. -/
def eval (f : Objective) (σ : ℕ → Bool) : ℤ := linVal σ f.lin + f.const

/-- The constraint `f ≥ b`. -/
def atLeast (f : Objective) (b : ℤ) : PBConstr := fromLinear f.lin (b - f.const)

theorem holds_atLeast (σ : ℕ → Bool) (f : Objective) (b : ℤ) :
    (f.atLeast b).Holds σ ↔ b ≤ f.eval σ := by
  rw [atLeast, holds_fromLinear_iff, eval]
  omega

private theorem linVal_map_neg (σ : ℕ → Bool) (L : List (ℕ × ℤ)) :
    linVal σ (L.map fun e => (e.1, -e.2)) = -linVal σ L := by
  induction L with
  | nil => simp
  | cons e L ih => simp only [List.map_cons, linVal_cons, ih]; ring

/-- **The objective-improving constraint** `f ≤ u - 1` (equation (3.6) of the documentation). -/
def improving (f : Objective) (u : ℤ) : PBConstr :=
  fromLinear (f.lin.map fun e => (e.1, -e.2)) (f.const - u + 1)

theorem holds_improving (σ : ℕ → Bool) (f : Objective) (u : ℤ) :
    (f.improving u).Holds σ ↔ f.eval σ < u := by
  rw [improving, holds_fromLinear_iff, linVal_map_neg, eval]
  omega

end Objective

/-- The value of an optional objective: a decision problem has the trivial objective `0` (§5 of
the documentation). -/
def objValue : Option Objective → (ℕ → Bool) → ℤ
  | some f, σ => f.eval σ
  | none, _ => 0

namespace Witness

/-- An entry `w x` of a linear form under the witness: the entries it becomes and the constant
it contributes. -/
def substEntry (ω : Witness) (e : ℕ × ℤ) : List (ℕ × ℤ) × ℤ :=
  match ω.find e.1 with
  | none => ([e], 0)
  | some .zero => ([], 0)
  | some .one => ([], e.2)
  | some (.lit (u, true)) => ([(u, e.2)], 0)
  | some (.lit (u, false)) => ([(u, -e.2)], e.2)

/-- A linear form under the witness: its linear part and its constant. -/
def substLin (ω : Witness) (L : List (ℕ × ℤ)) : List (ℕ × ℤ) × ℤ :=
  (L.flatMap fun e => (substEntry ω e).1, (L.map fun e => (substEntry ω e).2).sum)

private theorem linVal_append (σ : ℕ → Bool) (L L' : List (ℕ × ℤ)) :
    linVal σ (L ++ L') = linVal σ L + linVal σ L' := by
  simp [linVal]

private theorem linVal_apply (σ : ℕ → Bool) (ω : Witness) (L : List (ℕ × ℤ)) :
    linVal (apply σ ω) L = linVal σ (substLin ω L).1 + (substLin ω L).2 := by
  induction L with
  | nil => simp [substLin]
  | cons e L ih =>
    simp only [substLin] at ih ⊢
    rw [List.flatMap_cons, linVal_append, List.map_cons, List.sum_cons, linVal_cons, ih]
    suffices e.2 * ((apply σ ω e.1).toNat : ℤ) =
        linVal σ (substEntry ω e).1 + (substEntry ω e).2 by linarith
    obtain ⟨v, a⟩ := e
    unfold apply substEntry
    rcases ω.find v with _ | _ | _ | ⟨u, _ | _⟩ <;> simp [Literal.eval]
    cases σ u <;> simp

end Witness

/-! ### The `red` step -/

/-- A proof goal of a `red` step: `#1`, the constraint itself, `#2`, the objective, or a
constraint of the database by number. -/
inductive GoalId where
  /-- `#1`: the goal `C|ω`. -/
  | self
  /-- `#2`: the goal `f|ω ≤ f` of the objective `f`. The label is `#N + 2` for an order of `N`
  constraints (§5.4.1 of the documentation); there is no order here. -/
  | obj
  /-- The goal `D|ω` of the database constraint with this number. -/
  | db (n : ℕ)
  deriving DecidableEq, Repr

/-- An item of the subproof of a `red` step: a derivation step, which may use `¬C`, or a
`proofgoal` block, which starts from the negation of its goal and must derive the contradiction
it names. -/
inductive RedItem where
  /-- A derivation step. -/
  | step (s : Step)
  /-- `proofgoal g … qed : n`. -/
  | goal (g : GoalId) (sub : List Step) (qed : ℕ)
  deriving Repr

/-- A top-level step of a kernel proof: an implicational step, `red C : ω` with its subproof and
an optional closing contradiction `qed : n`, or the logging of a solution. -/
inductive TopStep where
  /-- An implicational step. -/
  | step (s : Step)
  /-- `red C : ω [: subproof … qed [: n]]`, with `none` for no subproof. Without a subproof,
  `¬C` takes no number and `C` takes the next one; with one, `¬C` takes the next number and `C`
  the number after the subproof (§5.5). -/
  | red (c : PBConstr) (ω : Witness) (sub : Option (List RedItem)) (qed : Option ℕ)
  /-- `sol ρ`: log the solution `ρ` (§5.8.1 of the documentation). -/
  | sol (ρ : List (Literal ℕ))
  /-- `soli ρ`: log the solution `ρ` and add the objective-improving constraint (§5.8.2). -/
  | soli (ρ : List (Literal ℕ))
  /-- `deld ids`: delete derived constraints (§5.7.1). -/
  | deld (ids : List ℕ)
  /-- `delc ids`: the unchecked deletion of core constraints (§5.7.1). -/
  | delc (ids : List ℕ)
  /-- `delc id : ω [: subproof … qed [: n]]`: the checked deletion of a core constraint, a
  redundance check against the remaining core set (§5.7.1), with `none` for no subproof. As for
  `red`, only a subproof gives `¬C` a number. -/
  | delcChecked (id : ℕ) (ω : Witness) (sub : Option (List RedItem)) (qed : Option ℕ)
  /-- `core id ids`: move constraints to the core set (§5.1). -/
  | core (ids : List ℕ)
  /-- `strengthening_to_core on` or `off` (§5.6). -/
  | strengthenToCore (on : Bool)
  /-- `obji v`: add the improving constraint `f ≤ v - 1` without a solution (§5.8.2). -/
  | obji (v : ℤ)
  /-- `obju new g` (`diff = false`) or `obju diff g` (`diff = true`), with an optional subproof
  of the goals `#1` and `#2` (§5.9). -/
  | obju (diff : Bool) (g : Objective) (sub : Option (List RedItem))
  /-- `solx ρ`: log the solution `ρ` and exclude every assignment that agrees with it on the
  preserved set (§5.8.3). -/
  | solx (ρ : List (Literal ℕ))
  deriving Repr

/-- The linear form `L - L'`: `L` with the coefficients of `L'` subtracted. -/
def subLinear (L L' : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  L'.foldr (fun e L => insertCoeff e.1 (-e.2) L) L

/-- **The objective goal** `f|ω ≤ f` of a `red` step (§5.4.1 of the documentation), as the
constraint `∑ᵥ wᵥ xᵥ - (f|ω - k') ≥ k'`, with `k'` the constant that `ω` moves out of `f`. -/
def objGoal (f : Objective) (ω : Witness) : PBConstr :=
  fromLinear (subLinear f.lin (Witness.substLin ω f.lin).1) (Witness.substLin ω f.lin).2

/-- The constraint of a goal: `C|ω`, `f|ω ≤ f` or `D|ω`, with `D` looked up in the database
`db₀` of the step. There is no goal `#2` without an objective. -/
def goalOf (obj : Option Objective) (db₀ : List (ℕ × PBConstr)) (ω : Witness) (c : PBConstr) :
    GoalId → Option PBConstr
  | .self => some (Witness.substC ω c)
  | .obj => obj.map (objGoal · ω)
  | .db n => (lookup db₀ n).map (Witness.substC ω)

/-- Run the items of a subproof whose goal labels name the constraints `goal`, collecting the goal
constraints proved by `proofgoal` blocks. A block's constraints are dropped after it; only the
numbering advances. -/
def runGoals (goal : GoalId → Option PBConstr) :
    List (ℕ × PBConstr) → ℕ → List RedItem → List PBConstr →
      Option (List (ℕ × PBConstr) × ℕ × List PBConstr)
  | db, n, [], proved => some (db, n, proved)
  | db, n, .step s :: items, proved =>
    match runStep db n s with
    | some (db', n') => runGoals goal db' n' items proved
    | none => none
  | db, n, .goal g sub q :: items, proved =>
    match goal g with
    | none => none
    | some G =>
      match subproofRefutes (fun db n => runSteps db n sub) db n G q with
      | some n' => runGoals goal db n' items (G :: proved)
      | none => none

/-- The sum of the positive coefficients of a linear form. -/
def posMass (L : List (ℕ × ℤ)) : ℕ := (L.map fun e => e.2.toNat).sum

/-- **Weak syntactic implication**: `D` implies `C` because the slack of `C` exceeds that of `D`
on every assignment. In the linear forms `∑ dᵥ xᵥ ≥ A` and `∑ cᵥ xᵥ ≥ B`, it suffices that
`B + ∑ᵥ max(0, dᵥ - cᵥ) ≤ A`. This holds when `C` follows from `D` by adding literal axioms. -/
def weakImplies (D C : PBConstr) : Bool :=
  decide (((C.degree : ℤ) - negSum C.terms) +
      posMass (subLinear (toLinear D.terms) (toLinear C.terms)) ≤
    (D.degree : ℤ) - negSum D.terms)

/-- `C` and `D` are the same constraint up to the order of their terms. -/
def sameUpToOrder (C D : PBConstr) : Bool := C.degree == D.degree && C.terms.isPerm D.terms

/-- A goal `G` of `obju` needs no subproof: it is trivially true after normalization, it is a
constraint of `core` up to the order of terms, or a `proofgoal` block proved it. -/
def objuCovered (core : List (ℕ × PBConstr)) (proved : List PBConstr) (G : PBConstr) : Bool :=
  G.normalize.degree == 0 || core.any (fun e => sameUpToOrder e.2 G.normalize) ||
    proved.contains G

/-- A goal constraint `G` needs no subproof, given the negation `negC` of the constraint being
added: it is covered as a goal of `obju` with the database `db₀`
(`Cslib.Logic.PL.VeriPB.objuCovered`), or `negC` weakly syntactically implies it. -/
def goalCovered (db₀ : List (ℕ × PBConstr)) (proved : List PBConstr) (negC G : PBConstr) :
    Bool :=
  objuCovered db₀ proved G || weakImplies negC G

/-- The end of a `red` subproof with premises `db₀` and goals for the constraints `gs`: the
closing constraint is a contradiction, or every goal is covered. -/
def redOk (obj : Option Objective) (db₀ gs : List (ℕ × PBConstr)) (ω : Witness) (c : PBConstr)
    (db' : List (ℕ × PBConstr)) (proved : List PBConstr) : Option ℕ → Bool
  | some q => namesContra db' q
  | none =>
    goalCovered db₀ proved c.negate (Witness.substC ω c) &&
      obj.all (fun f => goalCovered db₀ proved c.negate (objGoal f ω)) &&
      gs.all fun e => Witness.touchedTrue ω e.2 || weakImplies e.2 (Witness.substC ω e.2) ||
        goalCovered db₀ proved c.negate (Witness.substC ω e.2)

/-- **The redundance check with separate goals**: as `Cslib.Logic.PL.VeriPB.redCheck`, with
premises `db₀` but goals `D|ω` only for the constraints `D` of `gs`. In strengthening-to-core
mode, `gs` is the core set (§5.6 of the documentation); for a checked deletion, premises and goals
are the remaining core set (§5.7.1). -/
def redCheckOn (obj : Option Objective) (db₀ gs : List (ℕ × PBConstr)) (n : ℕ) (c : PBConstr)
    (ω : Witness) (items : List RedItem) (qed : Option ℕ) : Option ℕ :=
  match runGoals (goalOf obj db₀ ω c) ((n, c.negate) :: db₀) (n + 1) items [] with
  | none => none
  | some (db', n', proved) => if redOk obj db₀ gs ω c db' proved qed then some n' else none

/-- **The redundance check** of `red C : ω` for the objective `obj`: `¬C` takes the number `n`,
the subproof runs, and then either the closing contradiction is derived, or `C|ω` is covered, so
is `f|ω ≤ f` for an objective `f`, and so is `D|ω` for every constraint `D` of the database,
`D|ω` also when `ω` sets every literal of `D` it touches true. Returns the next number after the
subproof. -/
def redCheck (obj : Option Objective) (db₀ : List (ℕ × PBConstr)) (n : ℕ) (c : PBConstr)
    (ω : Witness) (items : List RedItem) (qed : Option ℕ) : Option ℕ :=
  redCheckOn obj db₀ db₀ n c ω items qed

/-! ### Objective updates -/

/-- The objective `f + g`, with the weights of each variable merged and zero weights dropped, as
CakePB's `add_obj` (§5.9 of the documentation). -/
def Objective.add (f g : Objective) : Objective :=
  ⟨((f.lin ++ g.lin).foldr (fun e L => insertCoeff e.1 e.2 L) []).filter (·.2 != 0),
    f.const + g.const⟩

private theorem linVal_filter_ne_zero (σ : ℕ → Bool) (L : List (ℕ × ℤ)) :
    linVal σ (L.filter (·.2 != 0)) = linVal σ L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    by_cases h : e.2 = 0 <;> simp [h, ih]

private theorem linVal_foldr_insertCoeff (σ : ℕ → Bool) (L : List (ℕ × ℤ)) :
    linVal σ (L.foldr (fun e L => insertCoeff e.1 e.2 L) []) = linVal σ L := by
  induction L with
  | nil => rfl
  | cons e L ih => rw [List.foldr_cons, linVal_insertCoeff, ih, linVal_cons]

@[simp] theorem Objective.eval_add (f g : Objective) (σ : ℕ → Bool) :
    (f.add g).eval σ = f.eval σ + g.eval σ := by
  simp only [Objective.add, Objective.eval, linVal_filter_ne_zero, linVal_foldr_insertCoeff]
  simp only [linVal, List.map_append, List.sum_append]
  ring

/-- The constraint `g ≥ h` between objectives. -/
def Objective.geGoal (g h : Objective) : PBConstr :=
  fromLinear (subLinear g.lin h.lin) (h.const - g.const)

/-- The goals of `obju` from `f` to `f'`: `#1` is `f' ≥ f` and `#2` is `f ≥ f'`. -/
def objuGoal (f f' : Objective) : GoalId → Option PBConstr
  | .self => some (f'.geGoal f)
  | .obj => some (f.geGoal f')
  | .db _ => none

/-- **The check of `obju`** from the objective `f` to `f'` (§5.9): goal `#1` is `f' ≥ f` and
goal `#2` is `f ≥ f'`, both derived from the core set `core` alone. Returns the next number after
the subproof. -/
def objuCheck (core : List (ℕ × PBConstr)) (n : ℕ) (f f' : Objective) (items : List RedItem) :
    Option ℕ :=
  match runGoals (objuGoal f f') core n items [] with
  | some (_, n', proved) =>
    if objuCovered core proved (f'.geGoal f) && objuCovered core proved (f.geGoal f') then
      some n'
    else none
  | none => none

/-! ### Solutions -/

/-- The assignment of a list of literals: a variable is true when it is listed positively, and
false otherwise. -/
def assignOf (ρ : List (Literal ℕ)) (v : ℕ) : Bool := ρ.contains (v, true)

/-- **A logged solution** `ρ` solves the constraints `cs` (§5.8.1 of the documentation, without
propagation as in the kernel format, §6.1): no literal is listed with its negation, and the
coefficients of the terms of each constraint whose literals are listed reach its degree. -/
def solves (ρ : List (Literal ℕ)) (cs : List PBConstr) : Bool :=
  ρ.all (fun l => !ρ.contains (Std.Sat.Literal.negate l)) &&
    cs.all fun c => decide (c.degree ≤ coeffSum (c.terms.filter fun t => ρ.contains t.2))

/-- `ρ` assigns every variable of `P`, as `solx` requires in the kernel format (§6.1). -/
def assignsAll (ρ : List (Literal ℕ)) (P : List ℕ) : Bool :=
  P.all fun x => ρ.contains (x, true) || ρ.contains (x, false)

/-- `ρ` assigns every variable of the objective, as `soli` requires (§5.8.2). -/
def assigns (ρ : List (Literal ℕ)) (f : Objective) : Bool := assignsAll ρ (f.lin.map (·.1))

/-- Lower the bound `d`, if any, to `v`. -/
private def lowerTo (d : Option ℤ) (v : ℤ) : Option ℤ := some (d.elim v (min · v))

/-! ### Preserved sets -/

/-- The values of the preserved variables `P` under `σ`: the projection of `σ` to `P`. -/
def proj (P : List ℕ) (σ : ℕ → Bool) : List Bool := P.map σ

/-- **The solution-excluding constraint** of `ρ` over `P` (§5.8.3): `∑ x` over the variables of
`P` false in `ρ`, plus `∑ ¬x` over those true, at least `1`. It holds exactly at the assignments
whose projection to `P` differs from that of `ρ`. A variable listed twice in `P` gives one term, so
the constraint is normalized: `preserved:` is a set (VeriPB and CakePB). -/
def exclusion (P : List ℕ) (ρ : List (Literal ℕ)) : PBConstr :=
  ⟨P.dedup.map fun x => (1, (x, !assignOf ρ x)), 1⟩

/-- The witness `ω` leaves the preserved variables, if any, alone (CakePB's `check_pres`). -/
def presFree (pres : Option (List ℕ)) (ω : Witness) : Bool :=
  pres.all fun P => ω.all fun e => !P.contains e.1

/-- The redundance check, with a witness that leaves the preserved variables alone. -/
def redCheckP (pres : Option (List ℕ)) (obj : Option Objective) (db₀ gs : List (ℕ × PBConstr))
    (n : ℕ) (c : PBConstr) (ω : Witness) (items : List RedItem) (qed : Option ℕ) : Option ℕ :=
  if presFree pres ω then redCheckOn obj db₀ gs n c ω items qed else none

/-! ### Proofs and the checker -/

/-- The state of the checker between top-level steps. -/
structure State where
  /-- The constraint database. -/
  db : List (ℕ × PBConstr)
  /-- The next constraint number. -/
  next : ℕ
  /-- The best value, if any, of a logged solution or of an `obji` step: the value that the lower
  bounds are checked against (CakePB's `dbound`). -/
  dbound : Option ℤ
  /-- The best value, if any, of a certifying logged solution: one logged while no unchecked
  deletion had happened, at its value under the objective of that time, or one that solves the
  input formula, at its value under the input objective. It certifies `SAT` and finite upper
  bounds (CakePB's `bound`). -/
  bound : Option ℤ
  /-- The core set: the constraints of the database that are core constraints (§3.4). -/
  core : List (ℕ × PBConstr)
  /-- No unchecked deletion of a core constraint has happened. -/
  chk : Bool
  /-- Strengthening-to-core mode is on (§5.6). -/
  tcb : Bool
  /-- The current objective, which `obju` changes (§5.9). -/
  obj : Option Objective
  /-- The preserved set, if any, from the input (`preserved:`); it does not change here. -/
  pres : Option (List ℕ)
  /-- The projections to the preserved set of the solutions logged by `solx`, latest first. -/
  logged : List (List Bool)
  deriving DecidableEq, Repr

/-- The initial state for the formula `F`, the objective `obj` and the preserved set `pres`: the
constraints, numbered from `1`, form the database and the core set. -/
def State.init (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) : State :=
  ⟨initDb F, F.length + 1, none, none, initDb F, true, false, obj, pres, []⟩

/-- Log the solution `ρ` of the database in the state `s` for the formula `F` and the input
objective `obj`. Its value under the current objective lowers `dbound`. It lowers `bound` too
if no unchecked deletion has happened, at that value, or else if it solves `F`, at its value
under the input objective. Any other solution leaves `bound` unchanged. -/
@[no_expose]
def State.log (F : List PBConstr) (obj : Option Objective) (s : State) (ρ : List (Literal ℕ)) :
    State :=
  { s with dbound := lowerTo s.dbound (objValue s.obj (assignOf ρ)),
           bound :=
             if s.chk then lowerTo s.bound (objValue s.obj (assignOf ρ))
             else if solves ρ (F.map normalize) then lowerTo s.bound (objValue obj (assignOf ρ))
             else s.bound }

/-- Add the constraint `c` to the database and the core set at the next number, as `soli`, `obji`
and `solx` do (§5.8). -/
private def State.addCore (s : State) (c : PBConstr) : State :=
  { s with db := (s.next, c) :: s.db, core := (s.next, c) :: s.core, next := s.next + 1 }

/-- Assert the value `v` of the objective `f` in the state `s`, the effect shared by `soli` and
`obji` (§5.8.2): the objective-improving constraint `f ≤ v - 1` joins the database and the core set
at the next number, and the bound `dbound` is lowered to `v`. -/
private def State.improve (f : Objective) (s : State) (v : ℤ) : State :=
  { s.addCore (f.improving v).normalize with dbound := lowerTo s.dbound v }

/-- The constraint numbers that a step deletes. -/
private def Step.delIds : Step → List ℕ
  | .del ids => ids
  | _ => []

/-- **One top-level step** for the input formula `F` and the objective `obj`.

* An implicational step adds a derived constraint. The untyped deletion `del id` of a core
  constraint counts as unchecked, and it is rejected in strengthening-to-core mode.
* `red` adds a derived constraint, or, in strengthening-to-core mode, a core constraint whose
  goals cover only the core set (§5.6).
* `sol` and `soli` log a solution of the database; `soli` adds its improving constraint to the
  core set (§5.8).
* `deld` deletes derived constraints; `delc` deletes core constraints unchecked, which in
  strengthening-to-core mode needs an empty derived set (§5.7.4).
* A checked `delc` of a core constraint `C` is a redundance check of `C` against the remaining
  core set alone, as in CakePB; in strengthening-to-core mode it is a proof by contradiction: its
  witness must be empty and its subproof must close with a contradiction `qed : n` (§5.7.4, as
  CakePB's `check_tcb_idopt`).
* `core id` moves constraints to the core set and needs at least one ID; promoting a constraint
  already in the core set changes nothing (§5.1). `strengthening_to_core on` moves all of them. -/
@[no_expose]
def stepTop (F : List PBConstr) (obj : Option Objective) (s : State) : TopStep → Option State
  | .step st =>
    match runStep s.db s.next st with
    | some (db', n') =>
      if s.tcb && s.core.any (fun e => st.delIds.contains e.1) then none
      else some { s with
        db := db', next := n',
        core := s.core.filter (fun e => !st.delIds.contains e.1),
        chk := s.chk && !s.core.any (fun e => st.delIds.contains e.1) }
    | none => none
  | .red c ω sub q =>
    match redCheckP s.pres s.obj s.db (if s.tcb then s.core else s.db) s.next c ω (sub.getD []) q
    with
    | some n' =>
      let m := if sub.isSome then n' else s.next
      some { s with
        db := (m, c.normalize) :: s.db, next := m + 1,
        core := if s.tcb then (m, c.normalize) :: s.core else s.core }
    | none => none
  | .sol ρ => if solves ρ (s.db.map (·.2)) then some (s.log F obj ρ) else none
  | .soli ρ =>
    match s.obj with
    | some f =>
      if solves ρ (s.db.map (·.2)) && assigns ρ f then
        some ((s.log F obj ρ).improve f (f.eval (assignOf ρ)))
      else none
    | none => none
  | .deld ids =>
    if decide ids.Nodup && ids.all (fun i => (lookup s.db i).isSome) &&
        !s.core.any (fun e => ids.contains e.1) then
      some { s with db := s.db.filter fun e => !ids.contains e.1 }
    else none
  | .delc ids =>
    if decide ids.Nodup && ids.all (fun i => s.core.any (·.1 == i)) &&
        (!s.tcb || s.db.all (s.core.contains ·)) then
      some { s with
        db := s.db.filter (fun e => !ids.contains e.1),
        core := s.core.filter (fun e => !ids.contains e.1), chk := false }
    else none
  | .delcChecked i ω sub q =>
    match lookup s.core i with
    | some c =>
      if s.core.all (fun e => e.1 != i || e.2 == c) && (!s.tcb || ω.isEmpty && q.isSome) then
        match redCheckP s.pres s.obj (s.core.filter (·.1 != i)) (s.core.filter (·.1 != i)) s.next
            c ω (sub.getD []) q with
        | some n' =>
          some { s with
            db := s.db.filter (·.1 != i), core := s.core.filter (·.1 != i),
            next := if sub.isSome then n' else s.next }
        | none => none
      else none
    | none => none
  | .core ids =>
    if !ids.isEmpty && ids.all fun i => (lookup s.db i).isSome then
      some { s with
        core := s.db.filter (fun e => ids.contains e.1 && !s.core.contains e) ++ s.core }
    else none
  | .strengthenToCore b =>
    some (if b then { s with core := s.db, tcb := true } else { s with tcb := false })
  | .obji v =>
    match s.obj with
    | some f => some (s.improve f v)
    | none => none
  | .obju diff g sub =>
    match s.obj with
    | some f =>
      match objuCheck s.core s.next f (if diff then f.add g else g) (sub.getD []) with
      | some n' =>
        some { s with
          obj := some (if diff then f.add g else g), next := n' }
      | none => none
    | none => none
  | .solx ρ =>
    match s.pres, s.obj with
    | some P, none =>
      if s.chk && solves ρ (s.db.map (·.2)) && assignsAll ρ P then
        some { (s.log F obj ρ).addCore (exclusion P ρ) with
          logged := proj P (assignOf ρ) :: s.logged }
      else none
    | _, _ => none

/-- Run the top-level steps for the input formula `F` and the objective `obj`. -/
def runTop (F : List PBConstr) (obj : Option Objective) : State → List TopStep → Option State
  | s, [] => some s
  | s, t :: ts =>
    match stepTop F obj s t with
    | some s' => runTop F obj s' ts
    | none => none

/-- The conclusion of a kernel proof (§4.3 of the documentation). -/
inductive Conclusion where
  /-- `conclusion UNSAT : q`: the constraint `q` is a contradiction. -/
  | unsat (q : ℕ)
  /-- `conclusion SAT [: ρ]`: certified by the assignment `ρ` if given, which must solve the input
  formula, and otherwise by a logged solution. -/
  | sat (asg : Option (List (Literal ℕ)))
  /-- `conclusion BOUNDS lb : q ub [: ρ]`, with `none` for `INF`: the optimum lies in `[lb, ub]`.
  For a finite `ub`, the assignment `ρ`, if given, must be a solution of the input of value `ub`;
  otherwise the bound `bound` certifies `ub`. -/
  | bounds (lb : Option ℤ) (q : ℕ) (ub : Option ℤ) (asg : Option (List (Literal ℕ)))
  /-- `conclusion NONE`: no claim. -/
  | noClaim
  /-- `conclusion ENUMERATION_PARTIAL n`: at least `n` solutions, counted by their projections
  to the preserved set. -/
  | enumPartial (n : ℕ)
  /-- `conclusion ENUMERATION_COMPLETE n : q`: exactly `n` solutions, counted by their
  projections to the preserved set, the contradiction `q` showing there are no others. -/
  | enumComplete (n : ℕ) (q : ℕ)
  deriving DecidableEq, Repr

/-- A kernel proof with redundance and solution-logging steps. -/
structure RedProof where
  /-- The steps. -/
  steps : List TopStep
  /-- The conclusion. -/
  conclusion : Conclusion
  deriving Repr

/-- The check of `BOUNDS lb : q ub [: ρ]` for the formula `F`, the input objective `f₀` and the
final objective `f` in the final state `s` (§4.3). The lower bound: for `INF`, `q` is a
contradiction, no solution was logged and no `obji` step was taken; otherwise `lb` is at most the
bound `dbound`, and `q` is a contradiction or weakly syntactically implies `f ≥ lb`. The upper
bound, unless `INF`: the assignment `ρ`, if given, solves `F`, assigns every variable of `f₀` and
has value `ub` under `f₀`; otherwise `bound` is `ub`. The bound need not be the value of a solution
of `F`; it guarantees that some solution of `F` has value at most `ub` under `f₀`. As in VeriPB,
an assignment after `INF` is not checked. -/
def boundsOk (F : List PBConstr) (f₀ f : Objective) (s : State) (lb : Option ℤ) (q : ℕ)
    (ub : Option ℤ) (asg : Option (List (Literal ℕ))) : Bool :=
  (match lb with
    | none => s.dbound.isNone && namesContra s.db q
    | some l =>
      s.dbound.all (fun d => decide (l ≤ d)) &&
        (namesContra s.db q || (lookup s.db q).any fun D => weakImplies D (f.atLeast l))) &&
  match ub, asg with
  | none, _ => true
  | some u, none => s.bound == some u
  | some u, some ρ => solves ρ (F.map normalize) && assigns ρ f₀ && f₀.eval (assignOf ρ) == u

/-- **The check of a conclusion** for the formula `F` and the input objective `obj` in the final
state `s` (§4.3).
* `UNSAT : q` needs the contradiction `q`, and `dbound` unset: no logged solution and no `obji`
  step.
* `SAT : ρ` needs `ρ` to solve `F`; `SAT` alone needs `bound` set, which guarantees some solution
  of `F` but need not come from one.
* `BOUNDS` needs an objective and `Cslib.Logic.PL.VeriPB.boundsOk`, the lower bound read against
  the final objective `s.obj`.
* `NONE` claims nothing and is always accepted once the steps check.

`UNSAT` and `SAT` are also accepted under an objective, an extension of this checker: §4.3 of the
documentation gives `BOUNDS` for optimization problems. -/
def checkConclusion (F : List PBConstr) (obj : Option Objective) (s : State) : Conclusion → Bool
  | .unsat q => s.dbound.isNone && namesContra s.db q
  | .sat none => s.bound.isSome
  | .sat (some ρ) => solves ρ (F.map normalize)
  | .bounds lb q ub asg =>
    match obj, s.obj with
    | some f₀, some f => boundsOk F f₀ f s lb q ub asg
    | _, _ => false
  | .noClaim => true
  | .enumPartial n => obj.isNone && s.pres.isSome && s.logged.length == n
  | .enumComplete n q =>
    obj.isNone && s.pres.isSome && s.logged.length == n && namesContra s.db q

/-- **The checker** for the formula `F`, the objective `obj` and the preserved set `pres`, if
any: run the steps from the formula, numbered from `1`, and check the conclusion. -/
def checkRed (F : List PBConstr) (obj : Option Objective) (P : RedProof)
    (pres : Option (List ℕ) := none) : Bool :=
  match runTop F obj (State.init F obj pres) P.steps with
  | some s => checkConclusion F obj s P.conclusion
  | none => false

/-! ### Soundness of `red` -/

theorem linVal_subLinear (σ : ℕ → Bool) (L L' : List (ℕ × ℤ)) :
    linVal σ (subLinear L L') = linVal σ L - linVal σ L' := by
  induction L' with
  | nil => simp [subLinear]
  | cons e L' ih =>
    simp only [subLinear, List.foldr_cons] at ih ⊢
    rw [linVal_insertCoeff, ih, linVal_cons]
    ring

/-- **The objective goal**: `σ` satisfies `f|ω ≤ f` exactly when `σ ∘ ω` has objective value at
most that of `σ`. -/
private theorem holds_objGoal (σ : ℕ → Bool) (f : Objective) (ω : Witness) :
    (objGoal f ω).Holds σ ↔ f.eval (Witness.apply σ ω) ≤ f.eval σ := by
  rw [objGoal, holds_fromLinear_iff, linVal_subLinear, Objective.eval, Objective.eval,
    Witness.linVal_apply]
  omega

theorem linVal_le_posMass (σ : ℕ → Bool) (L : List (ℕ × ℤ)) : linVal σ L ≤ posMass L := by
  induction L with
  | nil => simp [posMass]
  | cons e L ih =>
    simp only [posMass, List.map_cons, List.sum_cons, Nat.cast_add, linVal_cons] at ih ⊢
    have : e.2 * ((σ e.1).toNat : ℤ) ≤ (e.2.toNat : ℤ) := by
      cases σ e.1 <;> simp
    linarith

/-- **Weak syntactic implication is sound.** -/
theorem Holds.of_weakImplies {σ : ℕ → Bool} {D C : PBConstr} (hD : D.Holds σ)
    (h : weakImplies D C = true) : C.Holds σ := by
  rw [holds_iff_linVal] at hD ⊢
  have h1 := linVal_subLinear σ (toLinear D.terms) (toLinear C.terms)
  have h2 := linVal_le_posMass σ (subLinear (toLinear D.terms) (toLinear C.terms))
  have h3 := of_decide_eq_true h
  linarith

theorem Holds.of_sameUpToOrder {σ : ℕ → Bool} {C D : PBConstr} (hC : C.Holds σ)
    (h : sameUpToOrder C D = true) : D.Holds σ := by
  simp only [sameUpToOrder, Bool.and_eq_true, beq_iff_eq, List.isPerm_iff] at h
  unfold Holds lhs at hC ⊢
  rw [← h.1, ← (h.2.map _).sum_nat]
  exact hC

/-- A constraint of degree `0` after normalization is trivially true. -/
theorem holds_of_normalize_degree_eq_zero {σ : ℕ → Bool} {c : PBConstr}
    (h : c.normalize.degree = 0) : c.Holds σ := by
  rw [← holds_normalize]; unfold Holds; rw [h]; exact Nat.zero_le _

private theorem objuCovered_holds {σ : ℕ → Bool} {core : List (ℕ × PBConstr)}
    {proved : List PBConstr} {G : PBConstr} (hdb : AllHold σ core)
    (hp : ∀ G ∈ proved, G.Holds σ) (h : objuCovered core proved G = true) : G.Holds σ := by
  unfold objuCovered at h
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem] at h
  rcases h with (h | ⟨e, he, heq⟩) | h
  · exact holds_of_normalize_degree_eq_zero h
  · rw [← holds_normalize]; exact Holds.of_sameUpToOrder (hdb e he) heq
  · exact hp G h

theorem goalCovered_holds {σ : ℕ → Bool} {db₀ : List (ℕ × PBConstr)} {proved : List PBConstr}
    {negC G : PBConstr} (hdb : AllHold σ db₀) (hp : ∀ G ∈ proved, G.Holds σ)
    (hneg : negC.Holds σ) (h : goalCovered db₀ proved negC G = true) : G.Holds σ := by
  unfold goalCovered at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact objuCovered_holds hdb hp h
  · exact Holds.of_weakImplies hneg h

theorem runGoals_sound {σ : ℕ → Bool} {goal : GoalId → Option PBConstr} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (items : List RedItem) (proved : List PBConstr)
      (db' : List (ℕ × PBConstr)) (n' : ℕ) (proved' : List PBConstr),
      AllHold σ db → (∀ G ∈ proved, G.Holds σ) →
      runGoals goal db n items proved = some (db', n', proved') →
      AllHold σ db' ∧ ∀ G ∈ proved', G.Holds σ
  | db, n, [], proved, db', n', proved', hdb, hp, h => by
    simp only [runGoals, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨hdb, hp⟩
  | db, n, .step s :: items, proved, db', n', proved', hdb, hp, h => by
    simp only [runGoals] at h
    split at h
    · rename_i db₁ n₁ h₁
      exact runGoals_sound db₁ n₁ items proved db' n' proved' (runStep_sound _ _ _ _ _ hdb h₁) hp h
    · cases h
  | db, n, .goal g sub q :: items, proved, db', n', proved', hdb, hp, h => by
    simp only [runGoals] at h
    split at h
    · cases h
    · rename_i G hG
      split at h
      · rename_i n₁ h₁
        refine runGoals_sound db n₁ items (G :: proved) db' n' proved' hdb
          (List.forall_mem_cons.2 ⟨holds_of_subproofRefutes
            (fun _ _ hext hsub => runSteps_sound _ _ sub _ _ hext hsub) hdb h₁, hp⟩) h
      · cases h

/-- **The redundance check is sound**, with separate goals: an assignment `σ` satisfying the
premises `db₀` and the goal constraints `gs` either satisfies `C` too, or `σ ∘ ω` satisfies `gs`
and `C`. Either way, the objective does not increase. -/
theorem redCheckOn_sound {σ : ℕ → Bool} {obj : Option Objective}
    {db₀ gs : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr} {ω : Witness}
    {items : List RedItem} {qed : Option ℕ} (hdb : AllHold σ db₀) (hgs : AllHold σ gs)
    (h : redCheckOn obj db₀ gs n c ω items qed = some n') :
    ∃ τ, (τ = σ ∨ τ = Witness.apply σ ω) ∧ AllHold τ ((n', c.normalize) :: gs) ∧
      objValue obj τ ≤ objValue obj σ := by
  by_cases hc : c.Holds σ
  · exact ⟨σ, .inl rfl, List.forall_mem_cons.2 ⟨(holds_normalize σ c).2 hc, hgs⟩, le_rfl⟩
  unfold redCheckOn at h
  split at h
  · cases h
  rename_i db' n'' proved hrun
  have hnegC : c.negate.Holds σ := (holds_negate σ c).2 hc
  have hneg : AllHold σ ((n, c.negate) :: db₀) := List.forall_mem_cons.2 ⟨hnegC, hdb⟩
  obtain ⟨hall, hp⟩ := runGoals_sound _ _ _ [] db' n'' proved hneg (by simp) hrun
  split at h
  · rename_i hok
    cases h
    refine ⟨Witness.apply σ ω, .inr rfl, ?_⟩
    cases qed with
    | some q =>
      simp [redOk, hall.not_namesContra] at hok
    | none =>
      simp only [redOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hok
      obtain ⟨⟨hself, hobj⟩, hdbg⟩ := hok
      refine ⟨List.forall_mem_cons.2 ⟨?_, fun e he => ?_⟩, ?_⟩
      · rw [holds_normalize, ← Witness.holds_substC]
        exact goalCovered_holds hdb hp hnegC hself
      · rcases hdbg e he with (ht | hw) | hg
        · exact Witness.Holds.apply_of_touchedTrue ht (hgs e he)
        · rw [← Witness.holds_substC]; exact Holds.of_weakImplies (hgs e he) hw
        · rw [← Witness.holds_substC]; exact goalCovered_holds hdb hp hnegC hg
      · cases obj with
        | none => exact le_rfl
        | some f =>
          simp only [Option.all_some] at hobj
          exact (holds_objGoal σ f ω).1 (goalCovered_holds hdb hp hnegC hobj)
  · cases h

/-- **The redundance check is sound**: an assignment `σ` satisfying the database is either one
satisfying `C` too, or `σ ∘ ω` satisfies the database and `C`; either way, the objective does not
increase. -/
theorem redCheck_sound {σ : ℕ → Bool} {obj : Option Objective} {db₀ : List (ℕ × PBConstr)}
    {n n' : ℕ} {c : PBConstr} {ω : Witness} {items : List RedItem} {qed : Option ℕ}
    (hdb : AllHold σ db₀) (h : redCheck obj db₀ n c ω items qed = some n') :
    ∃ τ, AllHold τ ((n', c.normalize) :: db₀) ∧ objValue obj τ ≤ objValue obj σ := by
  obtain ⟨τ, -, hτ, hle⟩ := redCheckOn_sound hdb hdb h
  exact ⟨τ, hτ, hle⟩

/-! ### Soundness of solutions -/

private theorem coeffSum_filter_le {ts : List (ℕ × Literal ℕ)} {p q : ℕ × Literal ℕ → Bool}
    (h : ∀ t ∈ ts, p t = true → q t = true) :
    coeffSum (ts.filter p) ≤ coeffSum (ts.filter q) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ih := ih fun t' ht' => h t' (by simp [ht'])
    have ht := h t (by simp)
    simp only [List.filter_cons]
    cases hp : p t <;> cases hq : q t <;> simp_all; omega

/-- **A logged solution is a solution**: if `ρ` solves the constraints `cs`, the assignment of
`ρ` satisfies them. -/
theorem holds_of_solves {ρ : List (Literal ℕ)} {cs : List PBConstr} (h : solves ρ cs = true)
    {c : PBConstr} (hc : c ∈ cs) : c.Holds (assignOf ρ) := by
  simp only [solves, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  obtain ⟨hcons, hcs⟩ := h
  have heval : ∀ l ∈ ρ, Literal.eval (assignOf ρ) l = true := by
    rintro ⟨v, _ | _⟩ hl
    · have := hcons _ hl
      simp only [Std.Sat.Literal.negate, Bool.not_false] at this
      have hn : (v, true) ∉ ρ := fun h => by rw [List.contains_iff_mem.2 h] at this; cases this
      simp [Literal.eval, assignOf, hn]
    · simp [Literal.eval, assignOf, hl]
  unfold Holds
  rw [lhs_eq_coeffSum_filter]
  refine (hcs c hc).trans (coeffSum_filter_le fun t _ ht => heval t.2 ?_)
  simpa using ht

/-! ### Soundness of `obju` -/

theorem Objective.holds_geGoal (σ : ℕ → Bool) (g h : Objective) :
    (g.geGoal h).Holds σ ↔ h.eval σ ≤ g.eval σ := by
  rw [Objective.geGoal, holds_fromLinear_iff, linVal_subLinear, Objective.eval, Objective.eval]
  omega

/-- **The objective update is sound**: on every solution of the core set, the new objective
equals the old one. -/
theorem objuCheck_sound {σ : ℕ → Bool} {core : List (ℕ × PBConstr)} {n n' : ℕ}
    {f f' : Objective} {items : List RedItem} (hcore : AllHold σ core)
    (h : objuCheck core n f f' items = some n') : f'.eval σ = f.eval σ := by
  unfold objuCheck at h
  split at h
  · rename_i db' n'' proved hrun
    obtain ⟨-, hp⟩ := runGoals_sound _ _ _ [] db' n'' proved hcore (by simp) hrun
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      have h1 := (Objective.holds_geGoal σ f' f).1 (objuCovered_holds hcore hp hok.1)
      have h2 := (Objective.holds_geGoal σ f f').1 (objuCovered_holds hcore hp hok.2)
      omega
    · cases h
  · cases h

/-! ### Preserved sets: soundness -/

private theorem redCheckOn_of_redCheckP {pres : Option (List ℕ)} {obj : Option Objective}
    {db₀ gs : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr} {ω : Witness}
    {items : List RedItem} {qed : Option ℕ}
    (h : redCheckP pres obj db₀ gs n c ω items qed = some n') :
    presFree pres ω = true ∧ redCheckOn obj db₀ gs n c ω items qed = some n' := by
  unfold redCheckP at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

/-- A witness that leaves the preserved variables alone keeps every projection to them. -/
theorem proj_apply_of_presFree {pres : Option (List ℕ)} {ω : Witness}
    (h : presFree pres ω = true) (σ : ℕ → Bool) :
    ∀ P ∈ pres, proj P (Witness.apply σ ω) = proj P σ := by
  intro P hP
  simp only [presFree, Option.all_eq_true] at h
  have hω := h P hP
  simp only [proj, List.map_inj_left]
  intro x hx
  have hfind : Witness.find ω x = none := by
    simp only [Witness.find, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq]
    intro e he hex
    have := List.all_eq_true.1 hω e he
    simp [hex, hx] at this
  simp [Witness.apply, hfind]

/-- **The solution-excluding constraint** holds exactly where the projection differs from that of
`ρ`. -/
theorem holds_exclusion (σ : ℕ → Bool) (P : List ℕ) (ρ : List (Literal ℕ)) :
    (exclusion P ρ).Holds σ ↔ proj P σ ≠ proj P (assignOf ρ) := by
  have key : ∀ Q : List ℕ, 1 ≤ lhs σ (Q.map fun x => (1, (x, !assignOf ρ x))) ↔
      ∃ x ∈ Q, σ x ≠ assignOf ρ x := by
    intro Q
    induction Q with
    | nil => simp
    | cons x Q ih =>
      simp only [List.map_cons, lhs_cons, termVal, Literal.eval, List.mem_cons, exists_eq_or_imp,
        ← ih]
      cases σ x <;> cases assignOf ρ x <;> simp
  rw [Holds, exclusion, key]
  simp [proj, List.map_inj_left, List.mem_dedup]

/-! ### The invariants -/

private theorem holds_of_solves_normalize {ρ : List (Literal ℕ)} {F : List PBConstr}
    (h : solves ρ (F.map normalize) = true) : ∀ c ∈ F, c.Holds (assignOf ρ) := fun c hc =>
  (holds_normalize _ c).1 (holds_of_solves h (List.mem_map_of_mem hc))

private theorem Witness.apply_nil (σ : ℕ → Bool) : Witness.apply σ [] = σ := by
  funext v
  simp [Witness.apply, Witness.find]

private theorem allHold_filter {σ : ℕ → Bool} {db : List (ℕ × PBConstr)}
    (h : AllHold σ db) (p : ℕ × PBConstr → Bool) : AllHold σ (db.filter p) := fun e he =>
  h e (List.mem_filter.1 he).1

private theorem allHold_mono {σ : ℕ → Bool} {db db' : List (ℕ × PBConstr)}
    (hsub : ∀ e ∈ db', e ∈ db) (h : AllHold σ db) : AllHold σ db' := fun e he => h e (hsub e he)

private theorem holds_of_allHold_initDb {σ : ℕ → Bool} {F : List PBConstr}
    (h : AllHold σ (initDb F)) : ∀ c ∈ F, c.Holds σ := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
  have hmem : (j + 1, F[j].normalize) ∈ initDb F :=
    List.mem_map.2 ⟨(F[j], j), List.mem_iff_getElem.2 ⟨j, by simpa using hj, by
      rw [List.getElem_zipIdx]; simp⟩, rfl⟩
  exact (holds_normalize σ _).1 (h _ hmem)

/-- A step keeps every constraint of the database that it does not delete. -/
private theorem runStep_mem {db db' : List (ℕ × PBConstr)} {n n' : ℕ} {st : Step}
    (h : runStep db n st = some (db', n')) {e : ℕ × PBConstr} (he : e ∈ db)
    (hd : st.delIds.contains e.1 = false) : e ∈ db' := by
  cases st with
  | pol ops =>
    simp only [runStep] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.1 ▸ List.mem_cons_of_mem _ he
    · cases h
  | rup c hs =>
    simp only [runStep] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.1 ▸ List.mem_cons_of_mem _ he
    · cases h
  | rupSearch c =>
    simp only [runStep] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.1 ▸ List.mem_cons_of_mem _ he
    · cases h
  | pbc c sub q =>
    simp only [runStep, Option.map_eq_some_iff] at h
    obtain ⟨m, -, hm⟩ := h
    simp only [Prod.mk.injEq] at hm
    exact hm.1 ▸ List.mem_cons_of_mem _ he
  | del ids =>
    simp only [runStep] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, List.mem_filter]
      exact ⟨he, by simpa [Step.delIds] using hd⟩
    · cases h

/-- **The core invariant** of a state for the formula `F` and the input objective `obj`. -/
structure Inv (F : List PBConstr) (obj : Option Objective) (s : State) : Prop where
  /-- The core set is part of the database. -/
  sub : ∀ e ∈ s.core, e ∈ s.db
  /-- In strengthening-to-core mode, the core set implies the database (§5.6). -/
  imp : s.tcb = true → ∀ τ, AllHold τ s.core → AllHold τ s.db
  /-- While no unchecked deletion has happened, every solution of the core set gives a solution
  of `F` whose input objective value is at most its current objective value, and which agrees with
  it on the preserved set: CakePB's backward `bimp_pres_obj`, the injection being the identity on
  projections. -/
  chk : s.chk = true → ∀ τ, AllHold τ s.core →
    ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ objValue s.obj τ ∧
      ∀ P ∈ s.pres, proj P σ = proj P τ
  /-- The bound `bound` is at least the input objective value of a solution of `F`. -/
  wit : ∀ v ∈ s.bound, ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ v

theorem inv_init (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) :
    Inv F obj (State.init F obj pres) where
  sub _ he := he
  imp h := by simp [State.init] at h
  chk _ τ hτ := ⟨τ, holds_of_allHold_initDb hτ, le_rfl, fun _ _ => rfl⟩
  wit v hv := by simp [State.init] at hv

private theorem mem_lowerTo {d : Option ℤ} {u v : ℤ} (h : v ∈ lowerTo d u) : v = u ∨ v ∈ d := by
  cases d with
  | none =>
    simp only [lowerTo, Option.elim, Option.mem_def, Option.some.injEq] at h
    exact .inl h.symm
  | some e =>
    simp only [lowerTo, Option.elim, Option.mem_def, Option.some.injEq] at h
    rcases min_choice e u with hm | hm <;> rw [hm] at h
    · exact .inr (by simp [h])
    · exact .inl h.symm

/-- Logging a solution of the database keeps the invariant of `bound`. -/
private theorem wit_log {F : List PBConstr} {obj : Option Objective} {s : State}
    {ρ : List (Literal ℕ)} (hs : Inv F obj s) (hρ : solves ρ (s.db.map (·.2)) = true) :
    ∀ v ∈ (s.log F obj ρ).bound, ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ v := by
  intro v hv
  simp only [State.log] at hv
  split at hv
  · rename_i hc
    rcases mem_lowerTo hv with rfl | h
    · obtain ⟨σ, hσ, hle, -⟩ := hs.chk hc _ fun e he =>
        holds_of_solves hρ (List.mem_map_of_mem (f := (·.2)) (hs.sub e he))
      exact ⟨σ, hσ, hle⟩
    · exact hs.wit v h
  · split at hv
    · rename_i _ hF
      rcases mem_lowerTo hv with rfl | h
      · exact ⟨_, holds_of_solves_normalize hF, le_rfl⟩
      · exact hs.wit v h
    · exact hs.wit v hv

/-- Asserting an objective value keeps the core invariant: the improving constraint joins both the
core set and the database, and `bound` is unchanged. -/
private theorem inv_addCore {F : List PBConstr} {obj : Option Objective} {s : State}
    {c : PBConstr} (hs : Inv F obj s) : Inv F obj (s.addCore c) where
  sub e he := by
    rcases List.mem_cons.1 he with rfl | he
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hs.sub e he)
  imp ht τ hτ := List.forall_mem_cons.2 ⟨hτ _ List.mem_cons_self,
    hs.imp ht τ fun e he => hτ e (List.mem_cons_of_mem _ he)⟩
  chk hc τ hτ := hs.chk hc τ fun e he => hτ e (List.mem_cons_of_mem _ he)
  wit := hs.wit

/-- Asserting an objective value keeps the core invariant. -/
private theorem inv_improve {F : List PBConstr} {obj : Option Objective} {s : State}
    {f : Objective} {v : ℤ} (hs : Inv F obj s) : Inv F obj (s.improve f v) :=
  have h := inv_addCore (c := (f.improving v).normalize) hs
  ⟨h.sub, h.imp, h.chk, h.wit⟩

/-- The core set after a checked deletion of `i` gives back the whole core set once the deleted
constraint `c` holds. -/
private theorem allHold_core_of_filter {τ : ℕ → Bool} {core : List (ℕ × PBConstr)} {i : ℕ}
    {c : PBConstr} (hall : core.all (fun e => e.1 != i || e.2 == c) = true)
    (hr : AllHold τ (core.filter (·.1 != i))) (hc : c.Holds τ) : AllHold τ core := by
  intro e he
  by_cases hi : e.1 = i
  · have := List.all_eq_true.1 hall e he
    simp only [hi, bne_self_eq_false, Bool.false_or, beq_iff_eq] at this
    exact this ▸ hc
  · exact hr e (List.mem_filter.2 ⟨he, by simpa using hi⟩)

/-- **Each step keeps the core invariant.** -/
theorem stepTop_inv {F : List PBConstr} {obj : Option Objective} {s s' : State} {t : TopStep}
    (hs : Inv F obj s) (h : stepTop F obj s t = some s') : Inv F obj s' := by
  cases t with
  | step st =>
    simp only [stepTop] at h
    split at h
    · rename_i db' n' hrun
      split at h
      · cases h
      · rename_i htouch
        simp only [Option.some.injEq] at h
        subst h
        have hkeep : ∀ (hnt : (s.core.any fun e => st.delIds.contains e.1) = false),
            s.core.filter (fun e => !st.delIds.contains e.1) = s.core := fun hnt =>
          List.filter_eq_self.2 fun e he => by
            have := List.any_eq_false.1 hnt e he
            simpa using this
        refine ⟨fun e he => ?_, fun ht τ hτ => ?_, fun hc τ hτ => ?_, hs.wit⟩
        · rw [List.mem_filter] at he
          exact runStep_mem hrun (hs.sub e he.1) (by simpa using he.2)
        · have ht' : s.tcb = true := ht
          have hnt : (s.core.any fun e => st.delIds.contains e.1) = false := by
            simpa [ht'] using htouch
          rw [hkeep hnt] at hτ
          exact runStep_sound _ _ _ _ _ (hs.imp ht τ hτ) hrun
        · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          rw [hkeep hc.2] at hτ
          exact hs.chk hc.1 τ hτ
    · cases h
  | red c ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i n' hred
      simp only [Option.some.injEq] at h
      subst h
      generalize (if items.isSome = true then n' else s.next) = m
      refine ⟨fun e he => ?_, fun ht τ hτ => ?_, fun hc τ hτ => ?_, hs.wit⟩
      · split at he
        · rcases List.mem_cons.1 he with rfl | he
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hs.sub e he)
        · exact List.mem_cons_of_mem _ (hs.sub e he)
      · have ht' : s.tcb = true := ht
        simp only [ht', ↓reduceIte] at hτ
        exact List.forall_mem_cons.2 ⟨hτ _ List.mem_cons_self,
          hs.imp ht' τ fun e he => hτ e (List.mem_cons_of_mem _ he)⟩
      · refine hs.chk hc τ ?_
        split at hτ
        · exact fun e he => hτ e (List.mem_cons_of_mem _ he)
        · exact hτ
    · cases h
  | sol ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i hρ
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hs.sub, hs.imp, hs.chk, wit_log hs hρ⟩
    · cases h
  | soli ρ =>
    simp only [stepTop] at h
    split at h
    · split at h
      · rename_i f hρ
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hρ
        exact inv_improve ⟨hs.sub, hs.imp, hs.chk, wit_log hs hρ.1⟩
      · cases h
    · cases h
  | deld ids =>
    simp only [stepTop] at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hok
      refine ⟨fun e he => List.mem_filter.2 ⟨hs.sub e he, by simpa using hok.2 e he⟩,
        fun ht τ hτ => allHold_filter (hs.imp ht τ hτ) _, hs.chk, hs.wit⟩
    · cases h
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      refine ⟨fun e he => ?_, fun ht τ hτ => ?_, (fun hc => by cases hc), hs.wit⟩
      · rw [List.mem_filter] at he ⊢
        exact ⟨hs.sub e he.1, he.2⟩
      · rcases hok.2 with hf | hd
        · simp [hf] at ht
        · intro e he
          rw [List.mem_filter] at he
          exact hτ e (List.mem_filter.2
            ⟨List.contains_iff_mem.1 (List.all_eq_true.1 hd e he.1), he.2⟩)
    · cases h
  | delcChecked i ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i c hc
      split at h
      · rename_i hok
        split at h
        · rename_i n' hred
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
          have hback : ∀ τ, AllHold τ (s.core.filter (·.1 != i)) →
              ∃ τ', (τ' = τ ∨ τ' = Witness.apply τ ω) ∧ AllHold τ' s.core ∧
                objValue s.obj τ' ≤ objValue s.obj τ := fun τ hτ => by
            obtain ⟨τ', hτ', hall, hle⟩ := redCheckOn_sound hτ hτ (redCheckOn_of_redCheckP hred).2
            exact ⟨τ', hτ', allHold_core_of_filter hok.1 (fun e he => hall e
              (List.mem_cons_of_mem _ he)) ((holds_normalize _ _).1 (hall _ List.mem_cons_self)),
              hle⟩
          refine ⟨fun e he => ?_, fun ht τ hτ => ?_, fun hc τ hτ => ?_, hs.wit⟩
          · rw [List.mem_filter] at he ⊢
            exact ⟨hs.sub e he.1, he.2⟩
          · have hω : ω = [] := by
              rcases hok.2 with hf | hω
              · simp [hf] at ht
              · exact List.isEmpty_iff.1 hω.1
            obtain ⟨τ', hτ', hall, -⟩ := hback τ hτ
            have : τ' = τ := by rcases hτ' with rfl | rfl <;> simp [hω, Witness.apply_nil]
            subst this
            exact allHold_filter (hs.imp ht τ' hall) _
          · obtain ⟨τ', hτ', hall, hle⟩ := hback τ hτ
            obtain ⟨σ, hσ, hle', hp⟩ := hs.chk hc τ' hall
            refine ⟨σ, hσ, hle'.trans hle, fun P hP => (hp P hP).trans ?_⟩
            rcases hτ' with rfl | rfl
            · rfl
            · exact proj_apply_of_presFree (redCheckOn_of_redCheckP hred).1 τ P hP
        · cases h
      · cases h
    · cases h
  | core ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨fun e he => ?_, fun ht τ hτ => hs.imp ht τ fun e he => hτ e
        (List.mem_append_right _ he), fun hc τ hτ => hs.chk hc τ fun e he => hτ e
        (List.mem_append_right _ he), hs.wit⟩
      rcases List.mem_append.1 he with he | he
      · exact (List.mem_filter.1 he).1
      · exact hs.sub e he
    · cases h
  | strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h
    · exact ⟨hs.sub, (fun h => by cases h), hs.chk, hs.wit⟩
    · exact ⟨fun _ he => he, fun _ _ hτ => hτ,
        fun hc τ hτ => hs.chk hc τ (allHold_mono hs.sub hτ), hs.wit⟩
  | obji u =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact inv_improve hs
    · cases h
  | obju diff g sub =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · rename_i n' hobj
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨hs.sub, hs.imp, fun hc τ hτ => ?_, hs.wit⟩
        obtain ⟨σ, hσ, hle, hp⟩ := hs.chk hc τ hτ
        refine ⟨σ, hσ, ?_, hp⟩
        rw [hf] at hle
        simp only [objValue] at hle ⊢
        rw [objuCheck_sound hτ hobj]
        exact hle
      · cases h
    · cases h
  | solx ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i P hP hobj
      split at h
      · rename_i hok
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hok
        have h := inv_addCore (s := s.log F obj ρ) (c := exclusion P ρ)
          ⟨hs.sub, hs.imp, hs.chk, wit_log hs hok.1.2⟩
        exact ⟨h.sub, h.imp, h.chk, h.wit⟩
      · cases h
    · cases h

/-- **The lower-bound invariant** for a value `w`: some solution of the database has objective at
most `w`, or the bound `dbound` is at most `w`. -/
def Reaches (w : ℤ) (s : State) : Prop :=
  (∃ τ, AllHold τ s.db ∧ objValue s.obj τ ≤ w) ∨ ∃ d ∈ s.dbound, d ≤ w

/-- **The projected lower-bound invariant** for the variables `P`, a value `w` and an assignment
`σ₀`: some solution of the database that agrees with `σ₀` on `P` has objective at most `w`, or the
bound `dbound` is at most `w`. Over the solutions `σ₀` of the input, with `w` the value of `σ₀`
and `P` the preserved set, this is CakePB's forward `bimp_pres_obj` from the input to the
database below `dbound`, the injection being the identity on projections. -/
def ReachesOn (P : List ℕ) (w : ℤ) (σ₀ : ℕ → Bool) (s : State) : Prop :=
  (∃ τ, AllHold τ s.db ∧ objValue s.obj τ ≤ w ∧ proj P τ = proj P σ₀) ∨ ∃ d ∈ s.dbound, d ≤ w

/-- The lower-bound invariant is the projected one for no variable. -/
theorem reaches_iff_reachesOn_nil {w : ℤ} {σ₀ : ℕ → Bool} {s : State} :
    Reaches w s ↔ ReachesOn [] w σ₀ s := by
  simp [Reaches, ReachesOn, proj]

/-- The projected lower-bound invariant implies the plain one. -/
theorem reaches_of_reachesOn {P : List ℕ} {w : ℤ} {σ₀ : ℕ → Bool} {s : State}
    (h : ReachesOn P w σ₀ s) : Reaches w s := by
  rcases h with ⟨τ, hτ, hw, -⟩ | hb
  · exact .inl ⟨τ, hτ, hw⟩
  · exact .inr hb

private theorem exists_mem_lowerTo {d : Option ℤ} {w : ℤ} (u : ℤ) (h : ∃ v ∈ d, v ≤ w) :
    ∃ v ∈ lowerTo d u, v ≤ w := by
  obtain ⟨v, hv, hw⟩ := h
  simp only [Option.mem_def] at hv
  subst hv
  exact ⟨_, rfl, (min_le_left _ _).trans hw⟩

private theorem lowerTo_le (d : Option ℤ) (u : ℤ) : ∃ v ∈ lowerTo d u, v ≤ u := by
  cases d
  · exact ⟨u, rfl, le_rfl⟩
  · exact ⟨_, rfl, min_le_right _ _⟩

/-- Logging a solution keeps the projected lower-bound invariant: it only lowers `dbound`. -/
private theorem reachesOn_log {F : List PBConstr} {obj : Option Objective} {P : List ℕ} {w : ℤ}
    {σ₀ : ℕ → Bool} {s : State} {ρ : List (Literal ℕ)} (hs : ReachesOn P w σ₀ s) :
    ReachesOn P w σ₀ (s.log F obj ρ) := by
  rcases hs with hτ | hb
  · exact .inl hτ
  · exact .inr (exists_mem_lowerTo _ hb)

/-- Asserting the value `u` of the current objective `f` keeps the projected lower-bound
invariant: a solution of the database of value below `u` satisfies the improving constraint, and
otherwise `u`, the new bound, is at most `w`. -/
private theorem reachesOn_improve {f : Objective} {P : List ℕ} {w u : ℤ} {σ₀ : ℕ → Bool}
    {s : State} (hf : s.obj = some f) (hs : ReachesOn P w σ₀ s) :
    ReachesOn P w σ₀ (s.improve f u) := by
  simp only [ReachesOn, State.improve, State.addCore, hf] at hs ⊢
  by_cases hlt : ∃ τ, AllHold τ s.db ∧ objValue (some f) τ ≤ w ∧ proj P τ = proj P σ₀ ∧
      f.eval τ < u
  · obtain ⟨τ, hτ, hw, hp, hlt⟩ := hlt
    exact .inl ⟨τ, List.forall_mem_cons.2
      ⟨(holds_normalize _ _).2 ((Objective.holds_improving _ _ _).2 hlt), hτ⟩, hw, hp⟩
  · rcases hs with ⟨τ, hτ, hw, hp⟩ | hb
    · obtain ⟨v, hv, hle⟩ := lowerTo_le s.dbound u
      refine .inr ⟨v, hv, ?_⟩
      have hge : u ≤ f.eval τ := by
        by_contra hc
        exact hlt ⟨τ, hτ, hw, hp, by omega⟩
      simp only [objValue] at hw
      omega
    · exact .inr (exists_mem_lowerTo u hb)

/-- A solution of the database survives a checked `red` step: the repaired valuation, `τ` itself
or `τ ∘ ω`, satisfies the new constraint and the whole database, in strengthening-to-core mode by
the core invariant, without a larger objective value. -/
private theorem red_repair {F : List PBConstr} {obj : Option Objective} {s : State}
    {c : PBConstr} {ω : Witness} {items : List RedItem} {q : Option ℕ} {n₁ : ℕ} (m : ℕ)
    {τ : ℕ → Bool} (hinv : Inv F obj s) (hτ : AllHold τ s.db)
    (h₁ : redCheckOn s.obj s.db (if s.tcb then s.core else s.db) s.next c ω items q = some n₁) :
    ∃ τ', (τ' = τ ∨ τ' = Witness.apply τ ω) ∧ AllHold τ' ((m, c.normalize) :: s.db) ∧
      objValue s.obj τ' ≤ objValue s.obj τ := by
  have hgs : AllHold τ (if s.tcb then s.core else s.db) := by
    split
    · exact allHold_mono hinv.sub hτ
    · exact hτ
  obtain ⟨τ', hτ'eq, hτ', hle⟩ := redCheckOn_sound hτ hgs h₁
  refine ⟨τ', hτ'eq, List.forall_mem_cons.2
    ⟨(hτ' (n₁, c.normalize) List.mem_cons_self : c.normalize.Holds τ'), ?_⟩, hle⟩
  have hτ'' := fun e he => hτ' e (List.mem_cons_of_mem _ he)
  split at hτ''
  · rename_i ht
    exact hinv.imp ht τ' hτ''
  · exact hτ''

/-- **Each step keeps the projected lower-bound invariant**, for every value `w`, every
assignment `σ₀`, and variables `P` kept by every witness that leaves the preserved set alone: the
preserved set itself, or no variable. -/
theorem stepTop_reachesOn {F : List PBConstr} {obj : Option Objective} {P : List ℕ} {w : ℤ}
    {σ₀ : ℕ → Bool} {s s' : State} {t : TopStep} (hinv : Inv F obj s)
    (hP : ∀ ω, presFree s.pres ω = true → ∀ τ, proj P (Witness.apply τ ω) = proj P τ)
    (hs : ReachesOn P w σ₀ s) (h : stepTop F obj s t = some s') : ReachesOn P w σ₀ s' := by
  cases t with
  | step st =>
    simp only [stepTop] at h
    split at h
    · rename_i db₁ n₁ h₁
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        rcases hs with ⟨τ, hτ, hw, hp⟩ | hb
        · exact .inl ⟨τ, runStep_sound _ _ _ _ _ hτ h₁, hw, hp⟩
        · exact .inr hb
    · cases h
  | red c ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i n₁ h₁
      simp only [Option.some.injEq] at h
      subst h
      generalize (if items.isSome = true then n₁ else s.next) = m
      obtain ⟨hfree, h₁⟩ := redCheckOn_of_redCheckP h₁
      rcases hs with ⟨τ, hτ, hw, hp⟩ | hb
      · obtain ⟨τ', hτ'eq, hτ', hle⟩ := red_repair m hinv hτ h₁
        refine .inl ⟨τ', hτ', hle.trans hw, ?_⟩
        rcases hτ'eq with rfl | rfl
        · exact hp
        · exact (hP ω hfree τ).trans hp
      · exact .inr hb
    · cases h
  | sol ρ =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact reachesOn_log hs
    · cases h
  | soli ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact reachesOn_improve hf (reachesOn_log hs)
      · cases h
    · cases h
  | deld ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rcases hs with ⟨τ, hτ, hw, hp⟩ | hb
      · exact .inl ⟨τ, allHold_filter hτ _, hw, hp⟩
      · exact .inr hb
    · cases h
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rcases hs with ⟨τ, hτ, hw, hp⟩ | hb
      · exact .inl ⟨τ, allHold_filter hτ _, hw, hp⟩
      · exact .inr hb
    · cases h
  | delcChecked i ω items q =>
    simp only [stepTop] at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          rcases hs with ⟨τ, hτ, hw, hp⟩ | hb
          · exact .inl ⟨τ, allHold_filter hτ _, hw, hp⟩
          · exact .inr hb
        · cases h
      · cases h
    · cases h
  | core ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact hs
    · cases h
  | strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h <;>
      exact hs
  | obji u =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      simp only [Option.some.injEq] at h
      subst h
      exact reachesOn_improve hf hs
    · cases h
  | obju diff g sub =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · rename_i n' hobj
        simp only [Option.some.injEq] at h
        subst h
        simp only [ReachesOn, hf] at hs ⊢
        rcases hs with ⟨τ, hτ, hw, hp⟩ | hb
        · refine .inl ⟨τ, hτ, ?_, hp⟩
          simp only [objValue] at hw ⊢
          rw [objuCheck_sound (allHold_mono hinv.sub hτ) hobj]
          exact hw
        · exact .inr hb
      · cases h
    · cases h
  | solx ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i Q hQ hobj
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rcases hs with ⟨τ, hτ, hw, hp⟩ | hb
        · by_cases hex : (exclusion Q ρ).Holds τ
          · exact .inl ⟨τ, List.forall_mem_cons.2 ⟨hex, hτ⟩, hw, hp⟩
          · obtain ⟨v, hv, hle⟩ := lowerTo_le s.dbound (objValue s.obj (assignOf ρ))
            refine .inr ⟨v, hv, ?_⟩
            simp only [hobj, objValue] at hle hw
            omega
        · exact .inr (exists_mem_lowerTo _ hb)
      · cases h
    · cases h

/-- **Each step keeps the lower-bound invariant**, for every value `w`. -/
theorem stepTop_reaches {F : List PBConstr} {obj : Option Objective} {w : ℤ} {s s' : State}
    {t : TopStep} (hinv : Inv F obj s) (hs : Reaches w s)
    (h : stepTop F obj s t = some s') : Reaches w s' :=
  (reaches_iff_reachesOn_nil (σ₀ := fun _ => false)).2 (stepTop_reachesOn hinv
    (fun _ _ _ => rfl) (reaches_iff_reachesOn_nil.1 hs) h)

/-- A property kept by every step is kept by the checker. -/
theorem runTop_induct {F : List PBConstr} {obj : Option Objective} {P : State → Prop}
    (hstep : ∀ s t s', P s → stepTop F obj s t = some s' → P s') :
    ∀ (s : State) (ss : List TopStep) (s' : State), P s → runTop F obj s ss = some s' → P s'
  | s, [], s', hs, h => by
    simp only [runTop, Option.some.injEq] at h
    exact h ▸ hs
  | s, t :: ss, s', hs, h => by
    simp only [runTop] at h
    split at h
    · rename_i s₁ h₁
      exact runTop_induct hstep s₁ ss s' (hstep s t s₁ hs h₁) h
    · cases h

/-! ### The enumeration invariants -/

/-- **The backward enumeration invariant** for the formula `F`, the input objective `obj` and
the preserved set `pres`.
* The preserved set is `pres`, and without an input objective there is no current one.
* While no unchecked deletion has happened, the projection of no solution of the core set has
  been logged.
* The logged projections are distinct, and each is the projection of a solution of `F`.

With the core invariant (`Cslib.Logic.PL.VeriPB.Inv.chk`), by which every solution of the core
set agrees on `pres` with a solution of `F`, this is the counting half of CakePB's
`check_csteps_correct` that `ENUMERATION` uses. -/
structure EnumInv (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ))
    (s : State) : Prop where
  pres_eq : s.pres = pres
  obj_none : obj = none → s.obj = none
  nodup : s.logged.Nodup
  logsol : ∀ l ∈ s.logged, ∀ P ∈ pres, ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ proj P σ = l
  logcore : s.chk = true → ∀ τ, AllHold τ s.core → ∀ P ∈ pres, proj P τ ∉ s.logged

theorem enumInv_init (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) :
    EnumInv F obj pres (State.init F obj pres) where
  pres_eq := rfl
  obj_none h := h
  nodup := List.nodup_nil
  logsol l hl := by simp [State.init] at hl
  logcore _ _ _ _ _ h := by simp [State.init] at h

/-- A step that keeps the preserved set and the logged projections, and whose core solutions,
while `chk` holds, come from core solutions before it with the same projection, keeps the
backward enumeration invariant. -/
private theorem enumInv_of {F : List PBConstr} {obj : Option Objective} {pres : Option (List ℕ)}
    {s s' : State} (he : EnumInv F obj pres s) (hpres : s'.pres = s.pres)
    (hobj : s.obj = none → s'.obj = none) (hlog : s'.logged = s.logged)
    (hcore : s'.chk = true → s.chk = true ∧ ∀ τ, AllHold τ s'.core →
      ∃ τ', AllHold τ' s.core ∧ ∀ P ∈ pres, proj P τ' = proj P τ) :
    EnumInv F obj pres s' where
  pres_eq := hpres.trans he.pres_eq
  obj_none h := hobj (he.obj_none h)
  nodup := hlog ▸ he.nodup
  logsol l hl P hP := he.logsol l (hlog ▸ hl) P hP
  logcore hc τ hτ P hP := by
    obtain ⟨hc0, hback⟩ := hcore hc
    obtain ⟨τ', hτ', hag⟩ := hback τ hτ
    rw [hlog, ← hag P hP]
    exact he.logcore hc0 τ' hτ' P hP

/-- **Each step keeps the backward enumeration invariant.** -/
theorem stepTop_enumInv {F : List PBConstr} {obj : Option Objective} {pres : Option (List ℕ)}
    {s s' : State} {t : TopStep} (hinv : Inv F obj s) (he : EnumInv F obj pres s)
    (h : stepTop F obj s t = some s') : EnumInv F obj pres s' := by
  have same : ∀ τ, AllHold τ s.core → ∃ τ', AllHold τ' s.core ∧ ∀ P ∈ pres, proj P τ' = proj P τ :=
    fun τ hτ => ⟨τ, hτ, fun _ _ => rfl⟩
  have cons : ∀ e τ, AllHold τ (e :: s.core) →
      ∃ τ', AllHold τ' s.core ∧ ∀ P ∈ pres, proj P τ' = proj P τ :=
    fun _ τ hτ => ⟨τ, fun e he => hτ e (List.mem_cons_of_mem _ he), fun _ _ => rfl⟩
  cases t with
  | step st =>
    simp only [stepTop] at h
    split at h
    · split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        refine enumInv_of he rfl id rfl fun hc => ?_
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        have hkeep : s.core.filter (fun e => !st.delIds.contains e.1) = s.core :=
          List.filter_eq_self.2 fun e he => by
            have := List.any_eq_false.1 hc.2 e he
            simpa using this
        exact ⟨hc.1, fun τ hτ => same τ (by rw [← hkeep]; exact hτ)⟩
    · cases h
  | red c ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i n' hred
      simp only [Option.some.injEq] at h
      subst h
      generalize (if items.isSome = true then n' else s.next) = m
      refine enumInv_of he rfl id rfl fun hc => ⟨hc, fun τ hτ => ?_⟩
      split at hτ
      · exact cons _ τ hτ
      · exact same τ hτ
    · cases h
  | sol ρ =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact enumInv_of he rfl id rfl fun hc => ⟨hc, same⟩
    · cases h
  | soli ρ =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact enumInv_of he rfl id rfl fun hc => ⟨hc, cons _⟩
      · cases h
    · cases h
  | deld ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact enumInv_of he rfl id rfl fun hc => ⟨hc, same⟩
    · cases h
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact enumInv_of he rfl id rfl fun hc => by cases hc
    · cases h
  | delcChecked i ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i c hc
      split at h
      · rename_i hok
        split at h
        · rename_i n' hred
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at hok
          obtain ⟨hfree, hred⟩ := redCheckOn_of_redCheckP hred
          refine enumInv_of he rfl id rfl fun hc => ⟨hc, fun τ hτ => ?_⟩
          obtain ⟨τ', hτ', hall, -⟩ := redCheckOn_sound hτ hτ hred
          refine ⟨τ', allHold_core_of_filter hok.1 (fun e he => hall e
            (List.mem_cons_of_mem _ he)) ((holds_normalize _ _).1 (hall _ List.mem_cons_self)),
            fun P hP => ?_⟩
          rcases hτ' with rfl | rfl
          · rfl
          · exact proj_apply_of_presFree hfree τ P (he.pres_eq ▸ hP)
        · cases h
      · cases h
    · cases h
  | core ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact enumInv_of he rfl id rfl fun hc => ⟨hc, fun τ hτ =>
        ⟨τ, fun e he => hτ e (List.mem_append_right _ he), fun _ _ => rfl⟩⟩
    · cases h
  | strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h
    · exact enumInv_of he rfl id rfl fun hc => ⟨hc, same⟩
    · exact enumInv_of he rfl id rfl fun hc =>
        ⟨hc, fun τ hτ => ⟨τ, allHold_mono hinv.sub hτ, fun _ _ => rfl⟩⟩
  | obji u =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact enumInv_of he rfl id rfl fun hc => ⟨hc, cons _⟩
    · cases h
  | obju diff g sub =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact enumInv_of he rfl (fun h => by simp [hf] at h) rfl fun hc => ⟨hc, same⟩
      · cases h
    · cases h
  | solx ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i P hP hobj
      split at h
      · rename_i hok
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨hchk, hsol⟩, -⟩ := hok
        have hPp : P ∈ pres := by rw [← he.pres_eq, hP]; rfl
        have hpres : ∀ P' ∈ pres, P' = P := fun P' hP' => by
          rw [← he.pres_eq, hP] at hP'
          exact (Option.mem_some_iff.1 hP').symm
        have hρ : AllHold (assignOf ρ) s.core := fun e he =>
          holds_of_solves hsol (List.mem_map_of_mem (f := (·.2)) (hinv.sub e he))
        refine ⟨he.pres_eq, he.obj_none,
          List.nodup_cons.2 ⟨he.logcore hchk _ hρ P hPp, he.nodup⟩, fun l hl P' hP' => ?_,
          fun hc τ hτ P' hP' => ?_⟩
        · rw [hpres P' hP']
          rcases List.mem_cons.1 hl with rfl | hl
          · obtain ⟨σ, hσ, -, hp⟩ := hinv.chk hchk _ hρ
            exact ⟨σ, hσ, hp P hP⟩
          · exact he.logsol l hl P hPp
        · rw [hpres P' hP']
          have hex : (exclusion P ρ).Holds τ := hτ _ List.mem_cons_self
          rw [holds_exclusion] at hex
          intro hm
          rcases List.mem_cons.1 hm with heq | hm
          · exact hex heq
          · exact he.logcore hc τ (fun e he => hτ e (List.mem_cons_of_mem _ he)) P hPp hm
      · cases h
    · cases h

/-- **The forward enumeration invariant** for a solution `σ₀` of the formula: without an
objective, its projection to the preserved set is that of a solution of the database, or has
been logged. -/
def Covers (σ₀ : ℕ → Bool) (s : State) : Prop :=
  s.obj = none → ∀ P ∈ s.pres,
    (∃ τ, AllHold τ s.db ∧ proj P τ = proj P σ₀) ∨ proj P σ₀ ∈ s.logged

private theorem covers_of {σ₀ : ℕ → Bool} {s s' : State} (hc : Covers σ₀ s)
    (hpres : s'.pres = s.pres) (hobj : s'.obj = none → s.obj = none)
    (hlog : ∀ l ∈ s.logged, l ∈ s'.logged)
    (hdb : s.obj = none → ∀ P ∈ s.pres, ∀ τ, AllHold τ s.db →
      (∃ τ', AllHold τ' s'.db ∧ proj P τ' = proj P τ) ∨ proj P τ ∈ s'.logged) :
    Covers σ₀ s' := by
  intro ho P hP
  rw [hpres] at hP
  rcases hc (hobj ho) P hP with ⟨τ, hτ, hp⟩ | hl
  · rcases hdb (hobj ho) P hP τ hτ with ⟨τ', hτ', hp'⟩ | hl'
    · exact .inl ⟨τ', hτ', hp'.trans hp⟩
    · exact .inr (hp ▸ hl')
  · exact .inr (hlog _ hl)

/-- **Each step keeps the forward enumeration invariant.** -/
theorem stepTop_covers {F : List PBConstr} {obj : Option Objective} {σ₀ : ℕ → Bool}
    {s s' : State} {t : TopStep} (hinv : Inv F obj s) (hs : Covers σ₀ s)
    (h : stepTop F obj s t = some s') : Covers σ₀ s' := by
  have keep : ∀ db' : List (ℕ × PBConstr), (∀ τ, AllHold τ s.db → AllHold τ db') →
      s.obj = none → ∀ P ∈ s.pres, ∀ τ, AllHold τ s.db →
        (∃ τ', AllHold τ' db' ∧ proj P τ' = proj P τ) ∨ proj P τ ∈ s.logged :=
    fun _ hdb _ _ _ τ hτ => .inl ⟨τ, hdb τ hτ, rfl⟩
  cases t with
  | step st =>
    simp only [stepTop] at h
    split at h
    · rename_i db₁ n₁ h₁
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        exact covers_of hs rfl id (fun _ h => h)
          (keep _ fun τ hτ => runStep_sound _ _ _ _ _ hτ h₁)
    · cases h
  | red c ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i n₁ h₁
      simp only [Option.some.injEq] at h
      subst h
      generalize (if items.isSome = true then n₁ else s.next) = m
      obtain ⟨hfree, h₁⟩ := redCheckOn_of_redCheckP h₁
      refine covers_of hs rfl id (fun _ h => h) fun _ P hP τ hτ => .inl ?_
      obtain ⟨τ', hτ'eq, hτ', -⟩ := red_repair m hinv hτ h₁
      refine ⟨τ', hτ', ?_⟩
      rcases hτ'eq with rfl | rfl
      · rfl
      · exact proj_apply_of_presFree hfree τ P hP
    · cases h
  | sol ρ =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact covers_of hs rfl id (fun _ h => h) (keep _ fun _ h => h)
    · cases h
  | soli ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        intro ho
        simp [State.improve, State.addCore, State.log, hf] at ho
      · cases h
    · cases h
  | deld ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact covers_of hs rfl id (fun _ h => h) (keep _ fun τ hτ => allHold_filter hτ _)
    · cases h
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact covers_of hs rfl id (fun _ h => h) (keep _ fun τ hτ => allHold_filter hτ _)
    · cases h
  | delcChecked i ω items q =>
    simp only [stepTop] at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact covers_of hs rfl id (fun _ h => h) (keep _ fun τ hτ => allHold_filter hτ _)
        · cases h
      · cases h
    · cases h
  | core ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact covers_of hs rfl id (fun _ h => h) (keep _ fun _ h => h)
    · cases h
  | strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h <;>
      exact covers_of hs rfl id (fun _ h => h) (keep _ fun _ h => h)
  | obji u =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      simp only [Option.some.injEq] at h
      subst h
      intro ho
      simp [State.improve, State.addCore, hf] at ho
    · cases h
  | obju diff g sub =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        intro ho
        simp at ho
      · cases h
    · cases h
  | solx ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i P hP hobj
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        refine covers_of hs rfl id (fun _ h => List.mem_cons_of_mem _ h) fun _ P' hP' τ hτ => ?_
        have hP'P : P' = P := by rw [hP] at hP'; exact (Option.mem_some_iff.1 hP').symm
        subst hP'P
        by_cases hex : (exclusion P' ρ).Holds τ
        · exact .inl ⟨τ, List.forall_mem_cons.2 ⟨hex, hτ⟩, rfl⟩
        · rw [holds_exclusion, not_not] at hex
          exact .inr (hex ▸ List.mem_cons_self)
      · cases h
    · cases h

/-- **The invariants of a run.** The state after running the steps from the formula `F`, the
objective `obj` and the preserved set `pres` meets the core invariant and the backward
enumeration invariant; and, for every solution `σ` of `F`, the forward enumeration invariant and
the projected lower-bound invariant at the value of `σ`, for the preserved set and for no
variable. -/
theorem invariants_of_runTop {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {ss : List TopStep} {s : State}
    (h : runTop F obj (State.init F obj pres) ss = some s) :
    Inv F obj s ∧ EnumInv F obj pres s ∧ ∀ σ, (∀ c ∈ F, c.Holds σ) →
      Covers σ s ∧ ReachesOn (pres.getD []) (objValue obj σ) σ s := by
  have hie := runTop_induct (P := fun s => Inv F obj s ∧ EnumInv F obj pres s)
    (fun _ _ _ hs ht => ⟨stepTop_inv hs.1 ht, stepTop_enumInv hs.1 hs.2 ht⟩) _ _ s
    ⟨inv_init F obj pres, enumInv_init F obj pres⟩ h
  refine ⟨hie.1, hie.2, fun σ hσ => ⟨?_, ?_⟩⟩
  · exact (runTop_induct (P := fun s => Inv F obj s ∧ Covers σ s)
      (fun _ _ _ hs ht => ⟨stepTop_inv hs.1 ht, stepTop_covers hs.1 hs.2 ht⟩) _ _ s
      ⟨inv_init F obj pres, fun _ _ _ => .inl ⟨σ, allHold_initDb hσ, rfl⟩⟩ h).2
  · have hfree : ∀ s : State, EnumInv F obj pres s → ∀ ω, presFree s.pres ω = true →
        ∀ τ, proj (pres.getD []) (Witness.apply τ ω) = proj (pres.getD []) τ := by
      intro s he ω hω τ
      cases hP : pres with
      | none => rfl
      | some P => exact proj_apply_of_presFree hω τ P (by rw [he.pres_eq, hP]; rfl)
    exact (runTop_induct (P := fun s => Inv F obj s ∧ EnumInv F obj pres s ∧
        ReachesOn (pres.getD []) (objValue obj σ) σ s)
      (fun s _ _ hs ht => ⟨stepTop_inv hs.1 ht, stepTop_enumInv hs.1 hs.2.1 ht,
        stepTop_reachesOn hs.1 (hfree s hs.2.1) hs.2.2 ht⟩) _ _ s
      ⟨inv_init F obj pres, enumInv_init F obj pres,
        .inl ⟨σ, allHold_initDb hσ, le_rfl, rfl⟩⟩ h).2.2

/-! ### Soundness of the conclusions -/

variable {pres : Option (List ℕ)}

/-- The final state of an accepted proof meets the core invariant, and the lower-bound invariant
for the value of every solution of the formula. -/
private theorem reaches_of_checkRed {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    (h : checkRed F obj P pres = true) :
    ∃ s, checkConclusion F obj s P.conclusion = true ∧ Inv F obj s ∧
      ∀ σ, (∀ c ∈ F, c.Holds σ) → Reaches (objValue obj σ) s := by
  unfold checkRed at h
  split at h
  · rename_i s hrun
    obtain ⟨hinv, -, hσ⟩ := invariants_of_runTop hrun
    exact ⟨s, h, hinv, fun σ hσF => reaches_of_reachesOn (hσ σ hσF).2⟩
  · cases h

/-- **Soundness for `UNSAT`**: a formula with a checked proof of `UNSAT` has no solution. -/
theorem not_satisfiable_of_checkRed {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {q : ℕ} (h : checkRed F obj P pres = true) (hc : P.conclusion = .unsat q) (σ : ℕ → Bool) :
    ¬ ∀ c ∈ F, c.Holds σ := fun hF => by
  obtain ⟨s, hconc, -, hreach⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, Bool.and_eq_true, Option.isNone_iff_eq_none] at hconc
  obtain ⟨hbest, hq⟩ := hconc
  rcases hreach σ hF with ⟨τ, hτ, -⟩ | ⟨ρ, hρ, -⟩
  · simp [hτ.not_namesContra] at hq
  · simp [hbest] at hρ

/-- **Soundness for CNF**: a CNF whose clauses, as pseudo-Boolean constraints, have a checked
proof of `UNSAT` is unsatisfiable. -/
theorem not_satisfiable_cnf_of_checkRed {φ : CNF ℕ} {obj : Option Objective} {P : RedProof}
    {q : ℕ} (h : checkRed (φ.map Clause.toPB) obj P pres = true) (hc : P.conclusion = .unsat q) :
    ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  refine not_satisfiable_of_checkRed h hc σ fun c hc => ?_
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
  exact (Clause.holds_toPB_iff σ cl).2 ((CNF.eval_eq_true_iff σ φ).1 hσ cl hcl)

/-- **Soundness for `SAT : ρ`**: the stated assignment is a solution of the formula. -/
theorem holds_of_checkRed_sat {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {ρ : List (Literal ℕ)} (h : checkRed F obj P pres = true) (hc : P.conclusion = .sat (some ρ)) :
    ∀ c ∈ F, c.Holds (assignOf ρ) := by
  obtain ⟨s, hconc, -, -⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  exact holds_of_solves_normalize hconc

/-- **Soundness for `SAT`**: a formula with a checked proof of `SAT`, with or without an
assignment, has a solution. -/
theorem exists_satisfies_of_checkRed {F : List PBConstr} {obj : Option Objective}
    {P : RedProof} {asg : Option (List (Literal ℕ))} (h : checkRed F obj P pres = true)
    (hc : P.conclusion = .sat asg) : ∃ σ, ∀ c ∈ F, c.Holds σ := by
  cases asg with
  | none =>
    obtain ⟨s, hconc, hinv, -⟩ := reaches_of_checkRed h
    rw [hc] at hconc
    simp only [checkConclusion, Option.isSome_iff_exists] at hconc
    obtain ⟨ρ, hρ⟩ := hconc
    obtain ⟨σ, hσ, -⟩ := hinv.wit ρ hρ
    exact ⟨σ, hσ⟩
  | some ρ => exact ⟨_, holds_of_checkRed_sat h hc⟩

/-- An accepted `BOUNDS` conclusion has a final objective, and `boundsOk` holds for it. -/
private theorem boundsOk_of_checkConclusion {F : List PBConstr} {f : Objective} {s : State}
    {lb : Option ℤ} {q : ℕ} {ub : Option ℤ} {asg : Option (List (Literal ℕ))}
    (h : checkConclusion F (some f) s (.bounds lb q ub asg) = true) :
    ∃ f', s.obj = some f' ∧ boundsOk F f f' s lb q ub asg = true := by
  simp only [checkConclusion] at h
  cases hs : s.obj with
  | none => simp [hs] at h
  | some f' => exact ⟨f', rfl, by simpa [hs] using h⟩

/-- **Soundness for the lower bound of `BOUNDS`**: if the checker accepts
`conclusion BOUNDS lb : q ub` with a finite `lb` for the formula `F` and the objective `f`, then
every solution of `F` has objective at least `lb`. -/
theorem le_eval_of_checkRed {F : List PBConstr} {f : Objective} {P : RedProof} {lb : ℤ}
    {q : ℕ} {ub : Option ℤ} {asg : Option (List (Literal ℕ))}
    (h : checkRed F (some f) P pres = true)
    (hc : P.conclusion = .bounds (some lb) q ub asg) (σ : ℕ → Bool) (hσ : ∀ c ∈ F, c.Holds σ) :
    lb ≤ f.eval σ := by
  obtain ⟨s, hconc, -, hreach⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  obtain ⟨f', hf', hconc⟩ := boundsOk_of_checkConclusion hconc
  simp only [boundsOk, Bool.and_eq_true, Option.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Option.any_eq_true] at hconc
  obtain ⟨⟨hbest, hq⟩, -⟩ := hconc
  rcases hreach σ hσ with ⟨τ, hτ, hw⟩ | ⟨ρ, hρ, hw⟩
  · simp only [objValue, hf'] at hw
    rcases hq with hq | ⟨D, hD, himp⟩
    · simp [hτ.not_namesContra] at hq
    · exact ((Objective.holds_atLeast τ f' lb).1 (Holds.of_weakImplies (hτ.lookup hD) himp)).trans
        hw
  · exact (hbest ρ hρ).trans hw

/-- **Soundness for an infinite lower bound**: if the checker accepts
`conclusion BOUNDS INF : q ub` for the formula `F` and the objective `f`, then `F` has no
solution. -/
theorem not_satisfiable_of_checkRed_bounds {F : List PBConstr} {f : Objective} {P : RedProof}
    {q : ℕ} {ub : Option ℤ} {asg : Option (List (Literal ℕ))}
    (h : checkRed F (some f) P pres = true)
    (hc : P.conclusion = .bounds none q ub asg) (σ : ℕ → Bool) :
    ¬ ∀ c ∈ F, c.Holds σ := fun hF => by
  obtain ⟨s, hconc, -, hreach⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  obtain ⟨f', -, hconc⟩ := boundsOk_of_checkConclusion hconc
  simp only [boundsOk, Bool.and_eq_true, Option.isNone_iff_eq_none] at hconc
  obtain ⟨⟨hbest, hq⟩, -⟩ := hconc
  rcases hreach σ hF with ⟨τ, hτ, -⟩ | ⟨ρ, hρ, -⟩
  · simp [hτ.not_namesContra] at hq
  · simp [hbest] at hρ

/-- **Soundness for `BOUNDS lb : q ub : ρ`**: the stated assignment is a solution of the formula
with objective value exactly `ub`. -/
theorem holds_of_checkRed_bounds {F : List PBConstr} {f : Objective} {P : RedProof}
    {lb : Option ℤ} {q : ℕ} {ub : ℤ} {ρ : List (Literal ℕ)} (h : checkRed F (some f) P pres = true)
    (hc : P.conclusion = .bounds lb q (some ub) (some ρ)) :
    (∀ c ∈ F, c.Holds (assignOf ρ)) ∧ f.eval (assignOf ρ) = ub := by
  obtain ⟨s, hconc, -, -⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  obtain ⟨f', -, hconc⟩ := boundsOk_of_checkConclusion hconc
  simp only [boundsOk, Bool.and_eq_true, beq_iff_eq] at hconc
  obtain ⟨-, ⟨hsol, -⟩, hval⟩ := hconc
  exact ⟨holds_of_solves_normalize hsol, hval⟩

/-- **Soundness for the upper bound of `BOUNDS`**: if the checker accepts
`conclusion BOUNDS lb : q ub` with a finite `ub` for the formula `F` and the objective `f`, then
some solution of `F` has objective at most `ub`. With the lower bound
(`Cslib.Logic.PL.VeriPB.le_eval_of_checkRed`), the optimum lies in `[lb, ub]`. -/
theorem exists_eval_le_of_checkRed {F : List PBConstr} {f : Objective} {P : RedProof}
    {lb : Option ℤ} {q : ℕ} {ub : ℤ} {asg : Option (List (Literal ℕ))}
    (h : checkRed F (some f) P pres = true) (hc : P.conclusion = .bounds lb q (some ub) asg) :
    ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ f.eval σ ≤ ub := by
  cases asg with
  | none =>
    obtain ⟨s, hconc, hinv, -⟩ := reaches_of_checkRed h
    rw [hc] at hconc
    obtain ⟨f', -, hconc⟩ := boundsOk_of_checkConclusion hconc
    simp only [boundsOk, Bool.and_eq_true, beq_iff_eq] at hconc
    obtain ⟨-, hval⟩ := hconc
    exact hinv.wit ub hval
  | some ρ =>
    obtain ⟨hσ, hval⟩ := holds_of_checkRed_bounds h hc
    exact ⟨_, hσ, hval.le⟩

/-! ### Soundness of `ENUMERATION` -/

/-- The projections to `P` of the solutions of `F`: the solutions counted by a projected
enumeration (§4.3). -/
def projections (F : List PBConstr) (P : List ℕ) : Set (List Bool) :=
  {l | ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ proj P σ = l}

/-- The final state of an accepted proof meets the enumeration invariants. -/
private theorem enum_of_checkRed {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    (h : checkRed F obj P pres = true) :
    ∃ s, checkConclusion F obj s P.conclusion = true ∧ EnumInv F obj pres s ∧
      ∀ σ, (∀ c ∈ F, c.Holds σ) → Covers σ s := by
  unfold checkRed at h
  split at h
  · rename_i s hrun
    obtain ⟨-, he, hσ⟩ := invariants_of_runTop hrun
    exact ⟨s, h, he, fun σ hσF => (hσ σ hσF).1⟩
  · cases h

/-- An accepted `ENUMERATION` conclusion needs a preserved set. -/
theorem isSome_of_checkRed_enum {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {n : ℕ} (h : checkRed F obj P pres = true)
    (hc : P.conclusion = .enumPartial n ∨ ∃ q, P.conclusion = .enumComplete n q) :
    pres.isSome := by
  obtain ⟨s, hconc, he, -⟩ := enum_of_checkRed h
  rw [← he.pres_eq]
  rcases hc with hc | ⟨q, hc⟩ <;> rw [hc] at hconc <;>
    simp only [checkConclusion, Bool.and_eq_true] at hconc
  · exact hconc.1.2
  · exact hconc.1.1.2

/-- **Soundness of the enumeration count**: if the checker accepts
`conclusion ENUMERATION_PARTIAL n` or `conclusion ENUMERATION_COMPLETE n : q` for the formula
`F` with the preserved set `Pres`, then `F` has at least `n` solutions with distinct projections
to `Pres`. -/
theorem le_encard_of_checkRed_enum {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {Pres : List ℕ} {n : ℕ} (h : checkRed F obj P (some Pres) = true)
    (hc : P.conclusion = .enumPartial n ∨ ∃ q, P.conclusion = .enumComplete n q) :
    (n : ℕ∞) ≤ (projections F Pres).encard := by
  obtain ⟨s, hconc, he, -⟩ := enum_of_checkRed h
  have hlen : s.logged.length = n := by
    rcases hc with hc | ⟨q, hc⟩ <;> rw [hc] at hconc <;>
      simp only [checkConclusion, Bool.and_eq_true, beq_iff_eq] at hconc
    · exact hconc.2
    · exact hconc.1.2
  have hsub : (↑s.logged.toFinset : Set (List Bool)) ⊆ projections F Pres := fun l hl =>
    he.logsol l (by simpa using hl) Pres rfl
  calc (n : ℕ∞) = (↑s.logged.toFinset : Set (List Bool)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, List.toFinset_card_of_nodup he.nodup, hlen]
    _ ≤ _ := Set.encard_le_encard hsub

/-- **Soundness of a complete enumeration**: if the checker accepts
`conclusion ENUMERATION_COMPLETE n : q` for the formula `F` with the preserved set `Pres`, then
the solutions of `F` have exactly `n` distinct projections to `Pres`. -/
theorem encard_eq_of_checkRed_enumComplete {F : List PBConstr} {obj : Option Objective}
    {P : RedProof} {Pres : List ℕ} {n q : ℕ} (h : checkRed F obj P (some Pres) = true)
    (hc : P.conclusion = .enumComplete n q) : (projections F Pres).encard = n := by
  refine le_antisymm ?_ (le_encard_of_checkRed_enum h (.inr ⟨q, hc⟩))
  obtain ⟨s, hconc, he, hcov⟩ := enum_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hconc
  obtain ⟨⟨⟨hobj, -⟩, hlen⟩, hq⟩ := hconc
  have hsub : projections F Pres ⊆ (↑s.logged.toFinset : Set (List Bool)) := by
    rintro l ⟨σ, hσ, rfl⟩
    rcases hcov σ hσ (he.obj_none hobj) Pres (by rw [he.pres_eq]; rfl) with ⟨τ, hτ, -⟩ | hl
    · simp [hτ.not_namesContra] at hq
    · simpa using hl
  calc (projections F Pres).encard ≤ (↑s.logged.toFinset : Set (List Bool)).encard :=
        Set.encard_le_encard hsub
    _ = n := by
        rw [Set.encard_coe_eq_coe_finsetCard, List.toFinset_card_of_nodup he.nodup, hlen]

/-! ### Proofs without redundance and solutions -/

theorem runTop_map_step (F : List PBConstr) (obj : Option Objective) (s : State)
    (hs : s.tcb = false) (ss : List Step) :
    (runTop F obj s (ss.map .step)).map (fun s' => (s'.db, s'.dbound)) =
      (runSteps s.db s.next ss).map fun p => (p.1, s.dbound) := by
  induction ss generalizing s with
  | nil => rfl
  | cons st ss ih =>
    simp only [List.map_cons, runTop, runSteps, stepTop]
    rcases h : runStep s.db s.next st with _ | ⟨db', n'⟩
    · simp
    · simp only [hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ih _ rfl

/-- On proofs of `UNSAT` without `red` and solutions, the checker is the checker of
implicational steps. -/
theorem checkRed_map_step (F : List PBConstr) (obj : Option Objective) (P : Proof) :
    checkRed F obj ⟨P.steps.map .step, .unsat P.conclusion⟩ = check F P := by
  have hmap := runTop_map_step F obj (State.init F obj none) rfl P.steps
  unfold checkRed check
  simp only [State.init] at hmap ⊢
  rcases h1 : runTop F obj
      ⟨initDb F, F.length + 1, none, none, initDb F, true, false, obj, none, []⟩
      (P.steps.map .step) with _ | s <;>
    rcases h2 : runSteps (initDb F) (F.length + 1) P.steps with _ | ⟨db, n⟩ <;>
    simp_all [checkConclusion]

end VeriPB

end Cslib.Logic.PL

end
