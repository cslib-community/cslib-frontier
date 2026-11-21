/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.VeriPB
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
* The *witness* certifies `SAT` and finite upper bounds. It is the best logged solution that was
  logged while `chk` held, as in VeriPB and CakePB, or that solves the input formula, which this
  checker tests when the solution is logged (`Cslib.Logic.PL.VeriPB.State.log`). Any other
  logged solution never displaces the witness, even on a tie.

The conclusions (§4.3; `Cslib.Logic.PL.VeriPB.Conclusion`):
* `UNSAT : q` needs a contradiction `q`, no logged solution and no `obji` step.
* `SAT` needs a witness.
* `BOUNDS lb : q ub` needs an objective. The lower bound `lb` must be at most `dbound`, and `q`
  must be a contradiction or weakly syntactically imply `f ≥ lb`; `lb = INF` is checked as
  `UNSAT`. The upper bound `ub`, unless `INF`, must be the value of the witness.

§4.3 gives `BOUNDS` for optimization problems; accepting `UNSAT` and `SAT` under an objective as
well is an extension of this checker.

**The invariants.** Each step keeps two invariants (`Cslib.Logic.PL.VeriPB.stepTop_inv`,
`Cslib.Logic.PL.VeriPB.stepTop_reaches`), as CakePB's `check_csteps_correct` does (CakeML
commit `14856fcf`).
* *The core invariant* (`Cslib.Logic.PL.VeriPB.Inv`). The core set lies in the database. In
  strengthening-to-core mode, the core set implies the database, which justifies the smaller
  goal set of `red` there; this is `valid_conf` of CakePB. While `chk` holds, every solution of
  the core set gives a solution of the input formula with no larger objective value. Adding core
  constraints only shrinks the solutions of the core. A checked deletion of `C` repairs a
  solution of the remaining core into one of the whole core without raising the objective. So a
  witness gives an input solution of no larger value.
* *The lower-bound invariant* (`Cslib.Logic.PL.VeriPB.Reaches`). For a value `w`, either some
  solution of the database has objective at most `w`, or `dbound` is at most `w`.
  * An implicational step keeps every solution, and a deletion enlarges the set of solutions.
  * A `red` step repairs a solution without raising the objective. In strengthening-to-core
    mode, the repaired solution satisfies the core, hence the database.
  * `soli ρ` removes only solutions of objective at least `f(ρ)`, and lowers `dbound` to `f(ρ)`;
    `obji v` removes only solutions of objective at least `v`, and lowers `dbound` to `v`.

  Every solution `σ` of the formula meets this invariant initially for `w = f(σ)`, which gives
  the lower bounds. It is CakePB's invariant `bimp_obj`.

The soundness theorems follow CakePB's semantics of conclusions (`sem_concl`, `npbcScript.sml`).
In particular a finite upper bound `ub` certifies a solution of value at most `ub`.

**Scope.** There is no order, so no dominance and no order goals. Neither `solx` nor the
objective update `obju` (§5.9) is supported, nor deletion by specification and levels (§5.7.2).
The conclusions `NONE` and `ENUMERATION`, and the optional assignments of `SAT` and `BOUNDS`, are
not supported. Matching VeriPB, `red` steps are not cutting-planes steps, and the translation of
`Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check` covers only proofs without them.

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

## Main results

* `Cslib.Logic.PL.VeriPB.Witness.holds_substC`: `σ ⊨ D|ω` iff `σ ∘ ω ⊨ D`.
* `Cslib.Logic.PL.VeriPB.redCheck_sound`, `Cslib.Logic.PL.VeriPB.redCheckOn_sound`: a checked
  `red` step repairs a solution of the database without raising the objective.
* `Cslib.Logic.PL.VeriPB.stepTop_inv`, `Cslib.Logic.PL.VeriPB.stepTop_reaches`: the
  invariants.
* `Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_cnf_of_checkRed`: soundness for `UNSAT`.
* `Cslib.Logic.PL.VeriPB.exists_satisfies_of_checkRed`: soundness for `SAT`.
* `Cslib.Logic.PL.VeriPB.le_eval_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed_bounds`,
  `Cslib.Logic.PL.VeriPB.exists_eval_le_of_checkRed`: soundness for `BOUNDS`, its lower bound,
  infinite lower bound and upper bound.
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

/-- Run the items of a `red` subproof, collecting the goal constraints proved by `proofgoal`
blocks. A block's constraints are dropped after it; only the numbering advances. -/
def runItems (obj : Option Objective) (db₀ : List (ℕ × PBConstr)) (ω : Witness) (c : PBConstr) :
    List (ℕ × PBConstr) → ℕ → List RedItem → List PBConstr →
      Option (List (ℕ × PBConstr) × ℕ × List PBConstr)
  | db, n, [], proved => some (db, n, proved)
  | db, n, .step s :: items, proved =>
    match runStep db n s with
    | some (db', n') => runItems obj db₀ ω c db' n' items proved
    | none => none
  | db, n, .goal g sub q :: items, proved =>
    match goalOf obj db₀ ω c g with
    | none => none
    | some G =>
      match subproofRefutes (fun db n => runSteps db n sub) db n G q with
      | some n' => runItems obj db₀ ω c db n' items (G :: proved)
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

/-- A goal constraint `G` needs no subproof, given the negation `negC` of the constraint being
added: it is trivially true after normalization, it is a constraint of the database up to the
order of terms, a `proofgoal` block proved it, or `negC` weakly syntactically implies it. -/
def goalCovered (db₀ : List (ℕ × PBConstr)) (proved : List PBConstr) (negC G : PBConstr) :
    Bool :=
  G.normalize.degree == 0 || db₀.any (fun e => sameUpToOrder e.2 G.normalize) ||
    proved.contains G || weakImplies negC G

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
  match runItems obj db₀ ω c ((n, c.negate) :: db₀) (n + 1) items [] with
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

/-- `ρ` assigns every variable of the objective, as `soli` requires (§5.8.2). -/
def assigns (ρ : List (Literal ℕ)) (f : Objective) : Bool :=
  f.lin.all fun e => ρ.contains (e.1, true) || ρ.contains (e.1, false)

/-- Keep the better of the logged solution `best`, if any, and `ρ`; on a tie, `best`. -/
def record (obj : Option Objective) (best : Option (List (Literal ℕ))) (ρ : List (Literal ℕ)) :
    Option (List (Literal ℕ)) :=
  match best with
  | some ρ' => if objValue obj (assignOf ρ') ≤ objValue obj (assignOf ρ) then some ρ' else some ρ
  | none => some ρ

/-- Lower the bound `d`, if any, to `v`. -/
private def lowerTo (d : Option ℤ) (v : ℤ) : Option ℤ := some (d.elim v (min · v))

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
  /-- The best certifying logged solution, if any: one logged while no unchecked deletion had
  happened, or one that solves the input formula. It certifies `SAT` and finite upper bounds. -/
  witness : Option (List (Literal ℕ))
  /-- The core set: the constraints of the database that are core constraints (§3.4). -/
  core : List (ℕ × PBConstr)
  /-- No unchecked deletion of a core constraint has happened. -/
  chk : Bool
  /-- Strengthening-to-core mode is on (§5.6). -/
  tcb : Bool
  deriving DecidableEq, Repr

/-- The initial state for the formula `F`: its constraints, numbered from `1`, form the database
and the core set. -/
def State.init (F : List PBConstr) : State :=
  ⟨initDb F, F.length + 1, none, none, initDb F, true, false⟩

/-- Log the solution `ρ` of the database in the state `s` for the formula `F`: it competes for
`dbound` with its value, and for `witness` if no unchecked deletion has happened or it solves `F`.
Any other solution never displaces a witness. -/
@[no_expose]
def State.log (F : List PBConstr) (obj : Option Objective) (s : State) (ρ : List (Literal ℕ)) :
    State :=
  { s with dbound := lowerTo s.dbound (objValue obj (assignOf ρ)),
           witness := if s.chk || solves ρ (F.map normalize) then record obj s.witness ρ
             else s.witness }

/-- Assert the value `v` of the objective `f` in the state `s`, the effect shared by `soli` and
`obji` (§5.8.2): the objective-improving constraint `f ≤ v - 1` joins the database and the core set
at the next number, and the bound `dbound` is lowered to `v`. -/
private def State.improve (f : Objective) (s : State) (v : ℤ) : State :=
  { s with
    db := (s.next, (f.improving v).normalize) :: s.db,
    core := (s.next, (f.improving v).normalize) :: s.core,
    next := s.next + 1, dbound := lowerTo s.dbound v }

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
    match redCheckOn obj s.db (if s.tcb then s.core else s.db) s.next c ω (sub.getD []) q with
    | some n' =>
      let m := if sub.isSome then n' else s.next
      some { s with
        db := (m, c.normalize) :: s.db, next := m + 1,
        core := if s.tcb then (m, c.normalize) :: s.core else s.core }
    | none => none
  | .sol ρ => if solves ρ (s.db.map (·.2)) then some (s.log F obj ρ) else none
  | .soli ρ =>
    match obj with
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
        match redCheckOn obj (s.core.filter (·.1 != i)) (s.core.filter (·.1 != i)) s.next c ω
            (sub.getD []) q with
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
    match obj with
    | some f => some (s.improve f v)
    | none => none

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
  /-- `conclusion SAT`, certified by a logged solution. -/
  | sat
  /-- `conclusion BOUNDS lb : q ub`, with `none` for `INF`: the optimum lies in `[lb, ub]`. -/
  | bounds (lb : Option ℤ) (q : ℕ) (ub : Option ℤ)
  deriving DecidableEq, Repr

/-- A kernel proof with redundance and solution-logging steps. -/
structure RedProof where
  /-- The steps. -/
  steps : List TopStep
  /-- The conclusion. -/
  conclusion : Conclusion
  deriving Repr

/-- The check of `BOUNDS lb : q ub` for the objective `f` in the final state `s`. The lower
bound: for `INF`, `q` is a contradiction, no solution was logged and no `obji` step was taken;
otherwise `lb` is at most the bound `dbound`, and `q` is a contradiction or weakly syntactically
implies `f ≥ lb`. The upper bound, unless `INF`: the witness (the best certifying logged solution,
`Cslib.Logic.PL.VeriPB.State.witness`) has value `ub`. The witness need not solve the input
formula itself; it guarantees that some input solution has value at most `ub`. -/
def boundsOk (f : Objective) (s : State) (lb : Option ℤ) (q : ℕ) (ub : Option ℤ) : Bool :=
  (match lb with
    | none => s.dbound.isNone && namesContra s.db q
    | some l =>
      s.dbound.all (fun d => decide (l ≤ d)) &&
        (namesContra s.db q || (lookup s.db q).any fun D => weakImplies D (f.atLeast l))) &&
  match ub with
  | none => true
  | some u => s.witness.any fun ρ => f.eval (assignOf ρ) == u

/-- **The check of a conclusion** for the objective `obj` in the final state `s`. `UNSAT : q`
needs the contradiction `q`, no logged solution and no `obji` step; `SAT` a witness (a certifying
logged solution, which guarantees some input solution but need not be one itself); `BOUNDS` an
objective and `Cslib.Logic.PL.VeriPB.boundsOk`. `UNSAT` and `SAT` are also accepted under an
objective, an extension of this checker: §4.3 of the documentation gives `BOUNDS` for optimization
problems. -/
def checkConclusion (obj : Option Objective) (s : State) : Conclusion → Bool
  | .unsat q => s.dbound.isNone && namesContra s.db q
  | .sat => s.witness.isSome
  | .bounds lb q ub =>
    match obj with
    | some f => boundsOk f s lb q ub
    | none => false

/-- **The checker** for the formula `F` and the objective `obj`: run the steps from the
formula, numbered from `1`, and check the conclusion. -/
def checkRed (F : List PBConstr) (obj : Option Objective) (P : RedProof) : Bool :=
  match runTop F obj (State.init F) P.steps with
  | some s => checkConclusion obj s P.conclusion
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

theorem goalCovered_holds {σ : ℕ → Bool} {db₀ : List (ℕ × PBConstr)} {proved : List PBConstr}
    {negC G : PBConstr} (hdb : AllHold σ db₀) (hp : ∀ G ∈ proved, G.Holds σ)
    (hneg : negC.Holds σ) (h : goalCovered db₀ proved negC G = true) : G.Holds σ := by
  unfold goalCovered at h
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem] at h
  rcases h with ((h | ⟨e, he, heq⟩) | h) | h
  · rw [← holds_normalize]; unfold Holds; rw [h]; exact Nat.zero_le _
  · rw [← holds_normalize]; exact Holds.of_sameUpToOrder (hdb e he) heq
  · exact hp G h
  · exact Holds.of_weakImplies hneg h

theorem runItems_sound {σ : ℕ → Bool} {obj : Option Objective} {db₀ : List (ℕ × PBConstr)}
    {ω : Witness} {c : PBConstr} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (items : List RedItem) (proved : List PBConstr)
      (db' : List (ℕ × PBConstr)) (n' : ℕ) (proved' : List PBConstr),
      AllHold σ db → (∀ G ∈ proved, G.Holds σ) →
      runItems obj db₀ ω c db n items proved = some (db', n', proved') →
      AllHold σ db' ∧ ∀ G ∈ proved', G.Holds σ
  | db, n, [], proved, db', n', proved', hdb, hp, h => by
    simp only [runItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨hdb, hp⟩
  | db, n, .step s :: items, proved, db', n', proved', hdb, hp, h => by
    simp only [runItems] at h
    split at h
    · rename_i db₁ n₁ h₁
      exact runItems_sound db₁ n₁ items proved db' n' proved' (runStep_sound _ _ _ _ _ hdb h₁) hp h
    · cases h
  | db, n, .goal g sub q :: items, proved, db', n', proved', hdb, hp, h => by
    simp only [runItems] at h
    split at h
    · cases h
    · rename_i G hG
      split at h
      · rename_i n₁ h₁
        refine runItems_sound db n₁ items (G :: proved) db' n' proved' hdb
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
  obtain ⟨hall, hp⟩ := runItems_sound _ _ _ [] db' n'' proved hneg (by simp) hrun
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

/-- **The core invariant** of a state for the formula `F` and the objective `obj`. -/
structure Inv (F : List PBConstr) (obj : Option Objective) (s : State) : Prop where
  /-- The core set is part of the database. -/
  sub : ∀ e ∈ s.core, e ∈ s.db
  /-- In strengthening-to-core mode, the core set implies the database (§5.6). -/
  imp : s.tcb = true → ∀ τ, AllHold τ s.core → AllHold τ s.db
  /-- While no unchecked deletion has happened, every solution of the core set gives a solution
  of `F` with no larger objective value. -/
  chk : s.chk = true → ∀ τ, AllHold τ s.core →
    ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ objValue obj τ
  /-- The witness gives a solution of `F` with no larger objective value. -/
  wit : ∀ ρ ∈ s.witness,
    ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ objValue obj (assignOf ρ)

theorem inv_init (F : List PBConstr) (obj : Option Objective) : Inv F obj (State.init F) where
  sub _ he := he
  imp h := by simp [State.init] at h
  chk _ τ hτ := ⟨τ, holds_of_allHold_initDb hτ, le_rfl⟩
  wit ρ hρ := by simp [State.init] at hρ

private theorem mem_record {obj : Option Objective} {best : Option (List (Literal ℕ))}
    {ρ ρ' : List (Literal ℕ)} (h : ρ' ∈ record obj best ρ) : ρ' = ρ ∨ ρ' ∈ best := by
  unfold record at h
  split at h
  · split at h <;> simp only [Option.mem_def, Option.some.injEq] at h <;> subst h <;> simp_all
  · simp only [Option.mem_def, Option.some.injEq] at h
    exact .inl h.symm

/-- Logging a solution of the database keeps the witness invariant. -/
private theorem wit_log {F : List PBConstr} {obj : Option Objective} {s : State}
    {ρ : List (Literal ℕ)} (hs : Inv F obj s) (hρ : solves ρ (s.db.map (·.2)) = true) :
    ∀ ρ' ∈ (s.log F obj ρ).witness,
      ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ objValue obj (assignOf ρ') := by
  intro ρ' hρ'
  simp only [State.log] at hρ'
  split at hρ'
  · rename_i hc
    rcases mem_record hρ' with rfl | h
    · rcases Bool.or_eq_true _ _ ▸ hc with hc | hc
      · exact hs.chk hc _ fun e he =>
          holds_of_solves hρ (List.mem_map_of_mem (f := (·.2)) (hs.sub e he))
      · exact ⟨_, holds_of_solves_normalize hc, le_rfl⟩
    · exact hs.wit ρ' h
  · exact hs.wit ρ' hρ'

/-- Asserting an objective value keeps the core invariant: the improving constraint joins both the
core set and the database, and the witness is unchanged. -/
private theorem inv_improve {F : List PBConstr} {obj : Option Objective} {s : State}
    {f : Objective} {v : ℤ} (hs : Inv F obj s) : Inv F obj (s.improve f v) where
  sub e he := by
    rcases List.mem_cons.1 he with rfl | he
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hs.sub e he)
  imp ht τ hτ := List.forall_mem_cons.2 ⟨hτ _ List.mem_cons_self,
    hs.imp ht τ fun e he => hτ e (List.mem_cons_of_mem _ he)⟩
  chk hc τ hτ := hs.chk hc τ fun e he => hτ e (List.mem_cons_of_mem _ he)
  wit := hs.wit

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
                objValue obj τ' ≤ objValue obj τ := fun τ hτ => by
            obtain ⟨τ', hτ', hall, hle⟩ := redCheckOn_sound hτ hτ hred
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
          · obtain ⟨τ', -, hall, hle⟩ := hback τ hτ
            obtain ⟨σ, hσ, hle'⟩ := hs.chk hc τ' hall
            exact ⟨σ, hσ, hle'.trans hle⟩
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

/-- **The lower-bound invariant** for a value `w`: some solution of the database has objective at
most `w`, or the bound `dbound` is at most `w`. -/
def Reaches (obj : Option Objective) (w : ℤ) (s : State) : Prop :=
  (∃ τ, AllHold τ s.db ∧ objValue obj τ ≤ w) ∨ ∃ d ∈ s.dbound, d ≤ w

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

/-- Logging a solution keeps the lower-bound invariant: it only lowers `dbound`. -/
private theorem reaches_log {F : List PBConstr} {obj : Option Objective} {w : ℤ} {s : State}
    {ρ : List (Literal ℕ)} (hs : Reaches obj w s) : Reaches obj w (s.log F obj ρ) := by
  rcases hs with hτ | hb
  · exact .inl hτ
  · exact .inr (exists_mem_lowerTo _ hb)

/-- Asserting the value `u` of the objective keeps the lower-bound invariant: a solution of the
database of value below `u` satisfies the improving constraint, and otherwise `u`, the new bound,
is at most `w`. -/
private theorem reaches_improve {f : Objective} {w u : ℤ} {s : State}
    (hs : Reaches (some f) w s) : Reaches (some f) w (s.improve f u) := by
  by_cases hlt : ∃ τ, AllHold τ s.db ∧ objValue (some f) τ ≤ w ∧ f.eval τ < u
  · obtain ⟨τ, hτ, hw, hlt⟩ := hlt
    exact .inl ⟨τ, List.forall_mem_cons.2
      ⟨(holds_normalize _ _).2 ((Objective.holds_improving _ _ _).2 hlt), hτ⟩, hw⟩
  · rcases hs with ⟨τ, hτ, hw⟩ | hb
    · obtain ⟨v, hv, hle⟩ := lowerTo_le s.dbound u
      refine .inr ⟨v, hv, ?_⟩
      have hge : u ≤ f.eval τ := by
        by_contra hc
        exact hlt ⟨τ, hτ, hw, by omega⟩
      simp only [objValue] at hw
      omega
    · exact .inr (exists_mem_lowerTo u hb)

/-- A step that only deletes from the database keeps the lower-bound invariant. -/
private theorem reaches_filter {obj : Option Objective} {w : ℤ} {s : State}
    (p : ℕ × PBConstr → Bool) (hs : Reaches obj w s) :
    Reaches obj w { s with db := s.db.filter p } := by
  rcases hs with ⟨τ, hτ, hw⟩ | hb
  · exact .inl ⟨τ, allHold_filter hτ p, hw⟩
  · exact .inr hb

/-- **Each step keeps the lower-bound invariant**, for every value `w`. -/
theorem stepTop_reaches {F : List PBConstr} {obj : Option Objective} {w : ℤ} {s s' : State}
    {t : TopStep} (hinv : Inv F obj s) (hs : Reaches obj w s)
    (h : stepTop F obj s t = some s') : Reaches obj w s' := by
  cases t with
  | step st =>
    simp only [stepTop] at h
    split at h
    · rename_i db₁ n₁ h₁
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        rcases hs with ⟨τ, hτ, hw⟩ | hb
        · exact .inl ⟨τ, runStep_sound _ _ _ _ _ hτ h₁, hw⟩
        · exact .inr hb
    · cases h
  | red c ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i n₁ h₁
      simp only [Option.some.injEq] at h
      subst h
      generalize (if items.isSome = true then n₁ else s.next) = m
      rcases hs with ⟨τ, hτ, hw⟩ | hb
      · have hgs : AllHold τ (if s.tcb then s.core else s.db) := by
          split
          · exact allHold_mono hinv.sub hτ
          · exact hτ
        obtain ⟨τ', -, hτ', hle⟩ := redCheckOn_sound hτ hgs h₁
        refine .inl ⟨τ', List.forall_mem_cons.2
          ⟨(hτ' (n₁, c.normalize) List.mem_cons_self : c.normalize.Holds τ'), ?_⟩, hle.trans hw⟩
        have hτ'' := fun e he => hτ' e (List.mem_cons_of_mem _ he)
        split at hτ''
        · rename_i ht
          exact hinv.imp ht τ' hτ''
        · exact hτ''
      · exact .inr hb
    · cases h
  | sol ρ =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact reaches_log hs
    · cases h
  | soli ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i f
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact reaches_improve (reaches_log hs)
      · cases h
    · cases h
  | deld ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      exact h ▸ reaches_filter _ hs
    · cases h
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rcases hs with ⟨τ, hτ, hw⟩ | hb
      · exact .inl ⟨τ, allHold_filter hτ _, hw⟩
      · exact .inr hb
    · cases h
  | delcChecked i ω items q =>
    simp only [stepTop] at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          rcases hs with ⟨τ, hτ, hw⟩ | hb
          · exact .inl ⟨τ, allHold_filter hτ _, hw⟩
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
    · rename_i f
      simp only [Option.some.injEq] at h
      subst h
      exact reaches_improve hs
    · cases h

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

/-! ### Soundness of the conclusions -/

/-- The final state of an accepted proof meets the core invariant, and the lower-bound invariant
for the value of every solution of the formula. -/
private theorem reaches_of_checkRed {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    (h : checkRed F obj P = true) :
    ∃ s, checkConclusion obj s P.conclusion = true ∧ Inv F obj s ∧
      ∀ σ, (∀ c ∈ F, c.Holds σ) → Reaches obj (objValue obj σ) s := by
  unfold checkRed at h
  split at h
  · rename_i s hrun
    refine ⟨s, h, runTop_induct (fun _ _ _ => stepTop_inv) _ _ s (inv_init F obj) hrun,
      fun σ hσ => ?_⟩
    exact (runTop_induct (P := fun s => Inv F obj s ∧ Reaches obj (objValue obj σ) s)
      (fun _ _ _ hs ht => ⟨stepTop_inv hs.1 ht, stepTop_reaches hs.1 hs.2 ht⟩) _ _ s
      ⟨inv_init F obj, .inl ⟨σ, allHold_initDb hσ, le_rfl⟩⟩ hrun).2
  · cases h

/-- **Soundness for `UNSAT`**: a formula with a checked proof of `UNSAT` has no solution. -/
theorem not_satisfiable_of_checkRed {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {q : ℕ} (h : checkRed F obj P = true) (hc : P.conclusion = .unsat q) (σ : ℕ → Bool) :
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
    {q : ℕ} (h : checkRed (φ.map Clause.toPB) obj P = true) (hc : P.conclusion = .unsat q) :
    ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  refine not_satisfiable_of_checkRed h hc σ fun c hc => ?_
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
  exact (Clause.holds_toPB_iff σ cl).2 ((CNF.eval_eq_true_iff σ φ).1 hσ cl hcl)

/-- **Soundness for `SAT`**: a formula with a checked proof of `SAT` has a solution. -/
theorem exists_satisfies_of_checkRed {F : List PBConstr} {obj : Option Objective}
    {P : RedProof} (h : checkRed F obj P = true) (hc : P.conclusion = .sat) :
    ∃ σ, ∀ c ∈ F, c.Holds σ := by
  obtain ⟨s, hconc, hinv, -⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, Option.isSome_iff_exists] at hconc
  obtain ⟨ρ, hρ⟩ := hconc
  obtain ⟨σ, hσ, -⟩ := hinv.wit ρ hρ
  exact ⟨σ, hσ⟩

/-- **Soundness for the lower bound of `BOUNDS`**: if the checker accepts
`conclusion BOUNDS lb : q ub` with a finite `lb` for the formula `F` and the objective `f`, then
every solution of `F` has objective at least `lb`. -/
theorem le_eval_of_checkRed {F : List PBConstr} {f : Objective} {P : RedProof} {lb : ℤ}
    {q : ℕ} {ub : Option ℤ} (h : checkRed F (some f) P = true)
    (hc : P.conclusion = .bounds (some lb) q ub) (σ : ℕ → Bool) (hσ : ∀ c ∈ F, c.Holds σ) :
    lb ≤ f.eval σ := by
  obtain ⟨s, hconc, -, hreach⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, boundsOk, Bool.and_eq_true, Option.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Option.any_eq_true] at hconc
  obtain ⟨⟨hbest, hq⟩, -⟩ := hconc
  rcases hreach σ hσ with ⟨τ, hτ, hw⟩ | ⟨ρ, hρ, hw⟩
  · simp only [objValue] at hw
    rcases hq with hq | ⟨D, hD, himp⟩
    · simp [hτ.not_namesContra] at hq
    · exact ((Objective.holds_atLeast τ f lb).1 (Holds.of_weakImplies (hτ.lookup hD) himp)).trans
        hw
  · exact (hbest ρ hρ).trans hw

/-- **Soundness for an infinite lower bound**: if the checker accepts
`conclusion BOUNDS INF : q ub` for the formula `F` and the objective `f`, then `F` has no
solution. -/
theorem not_satisfiable_of_checkRed_bounds {F : List PBConstr} {f : Objective} {P : RedProof}
    {q : ℕ} {ub : Option ℤ} (h : checkRed F (some f) P = true)
    (hc : P.conclusion = .bounds none q ub) (σ : ℕ → Bool) : ¬ ∀ c ∈ F, c.Holds σ := fun hF => by
  obtain ⟨s, hconc, -, hreach⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, boundsOk, Bool.and_eq_true, Option.isNone_iff_eq_none] at hconc
  obtain ⟨⟨hbest, hq⟩, -⟩ := hconc
  rcases hreach σ hF with ⟨τ, hτ, -⟩ | ⟨ρ, hρ, -⟩
  · simp [hτ.not_namesContra] at hq
  · simp [hbest] at hρ

/-- **Soundness for the upper bound of `BOUNDS`**: if the checker accepts
`conclusion BOUNDS lb : q ub` with a finite `ub` for the formula `F` and the objective `f`, then
some solution of `F` has objective at most `ub`. With the lower bound
(`Cslib.Logic.PL.VeriPB.le_eval_of_checkRed`), the optimum lies in `[lb, ub]`. -/
theorem exists_eval_le_of_checkRed {F : List PBConstr} {f : Objective} {P : RedProof}
    {lb : Option ℤ} {q : ℕ} {ub : ℤ} (h : checkRed F (some f) P = true)
    (hc : P.conclusion = .bounds lb q (some ub)) :
    ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ f.eval σ ≤ ub := by
  obtain ⟨s, hconc, hinv, -⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, boundsOk, Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at hconc
  obtain ⟨-, ρ, hρ, hval⟩ := hconc
  obtain ⟨σ, hσ, hle⟩ := hinv.wit ρ hρ
  exact ⟨σ, hσ, hval ▸ hle⟩

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
  have hmap := runTop_map_step F obj (State.init F) rfl P.steps
  unfold checkRed check
  simp only [State.init] at hmap ⊢
  rcases h1 : runTop F obj ⟨initDb F, F.length + 1, none, none, initDb F, true, false⟩
      (P.steps.map .step) with _ | s <;>
    rcases h2 : runSteps (initDb F) (F.length + 1) P.steps with _ | ⟨db, n⟩ <;>
    simp_all [checkConclusion]

end VeriPB

end Cslib.Logic.PL

end
