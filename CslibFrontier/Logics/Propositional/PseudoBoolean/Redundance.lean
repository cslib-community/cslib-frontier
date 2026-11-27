/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.VeriPB
public import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Vector
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
(`Cslib.Logic.PL.VeriPB.objGoal`; label `#N + 2` for an order of `N` constraints), each to be
shown from the database and `¬C`; with an order loaded, also the order goals described below.

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
counts once.

**Changing the preserved set** (§5.10, §5.11.4). `preserved_add x : C` adds `x` to the current
preserved set `P` and `preserved_rm x : C` removes it (`Cslib.Logic.PL.VeriPB.presChangeCheck`,
CakePB's `check_change_pres`): the variables of `C` are in `P` and are not `x`, and the goals
`#1`, `x ⇒ C`, and `#2`, `x ⇐ C`, follow from the core set, each trivially or by a `proofgoal`
block, as the kernel format requires (§6.1). So `x ⇔ C` on every solution of the core set
(`Cslib.Logic.PL.VeriPB.presChangeCheck_sound`). `epreserved P` checks that the current preserved
set is `P`, as a set (`Cslib.Logic.PL.VeriPB.sameVars`). As CakePB's `update_pres`, adding a
variable already in `P` or removing one not in it leaves `P` as it is; VeriPB 3.0.2 rejects both
(`PreservedAddVariableAlreadyInSet`, `PreservedRemoveVariableNotInSet`). After a change, `solx`
is rejected, as §5.8.3 requires (CakePB accepts it), and the witnesses of `red`, `dom` and checked
deletion must leave the *current* preserved set alone, as in CakePB.

The conclusions keep their statements against the preserved set of the *input*: `ENUMERATION`
counts the projections of the input's solutions to the input's preserved set, which is what §4.3
claims about the input. An output section compares the input with an output formula preserving
the *final* set, and its guarantee is a bijection between the projections to the two sets
(CakePB's `sem_output`). The counting injections below carry the projections across each change:
`x ⇔ C` holds on the solutions of the core set, with `C` over variables of both sets, so the
projections to the old and to the new set determine each other
(`Cslib.Logic.PL.VeriPB.proj_eq_iff_of_presChangeCheck`). After a change, `solx` adds no
projection, so the logged projections, all taken before it, stay counted against the input's set,
and a final contradiction still shows every input projection logged. The order invariant follows
the current preserved set: a repair keeps `P`, hence `C`, hence `x` (`x ⇔ C` on the core set), as
CakePB's `sat_obj_po` follows `pres`.

**Orders** (§5.3). `def_order` defines an order `O⪯(u, v, a)` over its left variables `u`, right
variables `v` and auxiliary variables `a` (`Cslib.Logic.PL.VeriPB.Order`), by the constraints of a
*specification* `S⪯(u, v, a)` and of a *definition* `O⪯(u, v, a)`. It relates the value vectors
`x ⪯ y` when `∃ ρ, S⪯(x, y, ρ) ∧ O⪯(x, y, ρ)` (§5.4). An order without auxiliary variables has an
empty specification, and then `x ⪯ y` when `O⪯(x, y)` holds. The checks of `def_order`
(`Cslib.Logic.PL.VeriPB.Order.defCheck`), as in CakePB's `check_cstep`:
* the specification is derived from no premises by `red` steps whose witnesses set only
  auxiliary variables (CakePB's `check_spec`), so every assignment of `u` and `v` extends to one
  of `a` satisfying it (CakePB's `is_spec`);
* transitivity: from the premises `S⪯(u, v, a)`, `S⪯(v, w, b)`, `S⪯(u, w, c)`, `O⪯(u, v, a)`
  and `O⪯(v, w, b)`, numbered from `1`, for the fresh variables `w`, `b`, `c` of `fresh_right`,
  `fresh_aux_1` and `fresh_aux_2` (CakePB's `check_ws`), the goals of `O⪯(u, w, c)` are proved;
* reflexivity: from the premises `S⪯(u, u, a)`, the goals of `O⪯(u, u, a)` are proved, numbered
  after the transitivity proof, as in VeriPB and CakePB.

An accepted order is a specification and a preorder on vectors as long as `u`
(`Cslib.Logic.PL.VeriPB.Order.good_of_defCheck`). `load_order name z` applies it to the literals
`z`, of the same length and on no auxiliary variable (CakePB's `guard_ord_t`;
`Cslib.Logic.PL.VeriPB.LoadedOrder`), relating the assignments `α ⪯ β` when `z↾α ⪯ z↾β`; this is
a preorder (`Cslib.Logic.PL.VeriPB.LoadedOrder.isPreorder`), whose strict part is well founded
because it depends only on the finitely many values of `z`
(`Cslib.Logic.PL.VeriPB.LoadedOrder.wellFounded`). Loading an order moves every constraint to the
core set; `load_order;` unloads it. `eord_def` and `eord_loaded` (§5.11.3) check that a stored
order, or the loaded one and its literals, are as stated, and change nothing.

With an order loaded, `red C : ω` also has the order goals `O⪯(z↾ω, z, a)`, labelled `#2` …
`#N + 1` (§5.4.1), so that `α ∘ ω ⪯ α`; they are covered as `#1` is, or when `ω` leaves the
variables of `z` alone (§5.5.1, item 1c). Its subproof may enter the scope `scope leq`, which adds
the premises `S⪯(z↾ω, z, a)`; goals proved there count. If a scope is used or `ω` touches `z`,
the auxiliary variables must be *fresh* (CakePB's `check_fresh_aspo`,
`Cslib.Logic.PL.VeriPB.LoadedOrder.fresh`): they occur neither in the database, nor in `C`, nor
in the objective, nor in a value of `ω`. Then a solution `α` of the database violating `C` can be
given values of `a` satisfying `S⪯(z↾ω, z, a)`, as `S⪯` is a specification, without changing
anything else, and the goals hold there.

**Dominance** (§5.4.2). `dom C : ω` needs a loaded order whose auxiliary variables are fresh
(`Cslib.Logic.PL.VeriPB.domCheck`). From the database and `¬C`, it must derive `D|ω` only for the
constraints `D` of the core set, the order goals `O⪯(z↾ω, z, a)` (`#1` … `#N`), and the
objective goal (`#N + 2`), outside the scopes or in `scope leq`, which adds `S⪯(z↾ω, z, a)`; and a
`proofgoal #N + 1` block outside the scopes or in `scope geq`, which adds `S⪯(z, z↾ω, a)`, must
refute `O⪯(z, z↾ω, a)`. So `α ∘ ω` satisfies the core set and is strictly below `α`
(`Cslib.Logic.PL.VeriPB.domCheck_sound`). The constraint is derived, or core in
strengthening-to-core mode.

**Scopes** (§5.5). The constraints of a scope are dropped after it; only the numbering advances.
Each refuted `proofgoal` block is tagged with its scope, and a goal counts only when proved
outside the scopes or in a scope where it may be proved, as CakePB's `extract_scoped_pids`: for
`red`, `scope leq`; for `dom`, `scope geq` for goal `#N + 1` and `scope leq` for the others.
Scopes do not nest, and each may be entered more than once, as in VeriPB 3.0.2 and
CakePB. A goal proved in a scope where it does not count is not rejected but left to the other
coverage rules, as in CakePB; VeriPB 3.0.2 rejects it.

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
  as in CakePB (`CheckedDelete` in `check_cstep`). It does not check that `C` is the only core
  constraint with its number: the core invariant guarantees it.

In *strengthening-to-core mode* (§5.6), switched on by `strengthening_to_core on`, which moves
every constraint to the core, `red` adds core constraints, and its goals cover only the core set
and not the derived set. In this mode a checked deletion is a proof by contradiction: it takes no
witness and its subproof must end in a contradiction `qed : n`, as CakePB requires
(`check_tcb_idopt`); VeriPB 3.0.2 also accepts a subproof without it. An unchecked core deletion
needs an empty derived set (§5.7.4). The untyped deletion `del id` of the augmented format
(`Cslib.Logic.PL.VeriPB.Step.del`, §5.7.2) is unchecked when it deletes a core constraint, and this
checker rejects such a deletion in strengthening-to-core mode.

While an order is loaded (§5.7.4), as in strengthening-to-core mode, an unchecked deletion of core
constraints needs an empty derived set, and `del id` of a core constraint is rejected. A checked
deletion gets the order goals; as in VeriPB and CakePB, it may still take a witness, which
§5.7.4 forbids. Unloading with no order loaded (`load_order;`) is accepted, as VeriPB accepts it
and as §5.3 describes unloading as loading the empty order; CakePB rejects it (its
`UnloadOrder` needs a loaded order). A checked deletion that must check freshness checks it on its
premises, the remaining core set, and so accepts an auxiliary variable in a derived constraint, as
VeriPB does; CakePB's `check_fresh_aspo` scans the whole database and rejects it. This is sound,
since derived constraints are not premises of a checked deletion.

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
`Cslib.Logic.PL.VeriPB.stepTop_ordInv`, `Cslib.Logic.PL.VeriPB.stepTop_injInv`), as CakePB's
`check_csteps_correct` does (CakeML commit `14856fcf`); they hold after every run
(`Cslib.Logic.PL.VeriPB.invariants_of_runTop`).
* *The core invariant* (`Cslib.Logic.PL.VeriPB.Inv`). The core set lies in the database. In
  strengthening-to-core mode, the core set implies the database, which justifies the smaller
  goal set of `red` there; this is `valid_conf` of CakePB. While `chk` holds, every solution of
  the core set gives a solution of the input formula with no larger objective value, so `bound`
  is at least the input value of some input solution. The numbers of the database are distinct
  and below the next number, as CakePB's `id_ok` (`Cslib.Logic.PL.VeriPB.IdOk`): every step
  numbers its new constraints, and those of its subproofs, from the next number on. So two core
  constraints with the same number are the same.
* *The counting injections* (`Cslib.Logic.PL.VeriPB.InjInv`), CakePB's `bimp_pres_obj` with the
  logged projections of its `bimp_pres`. For each bound `v` on the objective, there are
  injections between the projections of the solutions of value at most `v`:
  * forward, below `dbound` or without an objective, from the projections to the input's preserved
    set of the input's solutions into those to the current preserved set of the database's
    solutions, together with the logged projections;
  * backward, from the projections to the current preserved set of the core set's solutions,
    while `chk` holds, together with the logged projections, into those of the input's
    solutions.

  The logged projections are counted by their indices. While the preserved set is unchanged both
  injections are the identity on projections of solutions. They rest on what one step does to
  one solution:
  * forward (`Cslib.Logic.PL.VeriPB.stepTop_fwd`): an implicational step keeps every solution of
    the database, a deletion enlarges the set of solutions, and a `red` step repairs a solution
    without raising the objective or moving a preserved variable (in strengthening-to-core mode,
    the repaired solution satisfies the core, hence the database); `soli ρ` and `obji v` cut off
    only solutions of objective at least the new `dbound`, and `solx` only those of the projection
    it logs;
  * backward (`Cslib.Logic.PL.VeriPB.stepTop_back`): adding core constraints only shrinks the
    solutions of the core, a checked deletion of `C` repairs a solution of the remaining core into
    one of the whole core without raising the objective, with a witness that leaves the preserved
    set alone, and `obju` keeps the objective's values on the core;
  * a change of the preserved set composes both injections with the bijection between the old and
    the new projections.

  Their existence halves are the lower-bound invariant (`Cslib.Logic.PL.VeriPB.Reaches`,
  CakePB's `bimp_obj`; `Cslib.Logic.PL.VeriPB.InjInv.reaches`): some solution of the database has
  objective at most the value of a solution of the input, or `dbound` is at most it, which gives
  the lower bounds. Their counting halves give the count of `ENUMERATION`
  (`Cslib.Logic.PL.VeriPB.projections`): the backward injection maps the logged projections into
  the input's projected solutions, and once the database has no solution the forward injection
  maps those into the logged ones. The output sections
  (`CslibFrontier.Logics.Propositional.PseudoBoolean.Output`) rest on them. The backward injection
  holds for every `v`, not only below `bound` as in CakePB.
* *The order invariant* (`Cslib.Logic.PL.VeriPB.OrdInv`, `Cslib.Logic.PL.VeriPB.stepTop_ordInv`):
  every defined order is good, and while an order is loaded every solution of the core set gives
  a solution of the database below it in the order, of no larger objective value and with the same
  projection (`Cslib.Logic.PL.VeriPB.SatObjPo`, CakePB's `sat_obj_po` in `valid_conf`). Loading an
  order makes the core set the database, where it holds by reflexivity; each later step keeps it,
  `red` by transitivity. It is what `dom`, whose goals cover only the core set, needs: a solution
  of the database violating `C` is mapped by `ω` to a solution of the core set strictly below it,
  and so, by the invariant, to a solution of the database below it, and so on. As the strict part
  of the order is well founded, this ends at a solution of the database and `C`, below the first
  in the order and the objective, with the same projection
  (`Cslib.Logic.PL.VeriPB.SatObjPo.dom`, CakePB's `dominance_conf_valid`). This keeps the forward
  injection through `dom`.

**Monotonicity** (`Cslib.Logic.PL.VeriPB.Mono`, `Cslib.Logic.PL.VeriPB.stepTop_mono`,
`Cslib.Logic.PL.VeriPB.runTop_mono`), as CakePB's `check_csteps_correct` states it: the numbering
only advances, `dbound` and `bound` only decrease, `chk` is never restored, and the logged
projections only grow and, without `chk`, are frozen. Without `chk`, CakePB also freezes `bound`;
here it can still fall to the input value of a logged solution that solves the input formula.

The soundness theorems follow CakePB's semantics of conclusions (`sem_concl`, `npbcScript.sml`).
In particular a finite upper bound `ub` certifies a solution of value at most `ub`.

**Scope.** Neither deletion by specification and levels (§5.7.2) is supported, nor `UNSAT`
without a constraint ID (the kernel format requires one). Matching VeriPB, `red` and `dom` steps
are not cutting-planes steps, and the translation of
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
* `Cslib.Logic.PL.VeriPB.Order`, `Cslib.Logic.PL.VeriPB.Order.defCheck`,
  `Cslib.Logic.PL.VeriPB.LoadedOrder`: orders, the check of `def_order`, and loaded orders.
* `Cslib.Logic.PL.VeriPB.domCheck`: the check of `dom`.
* `Cslib.Logic.PL.VeriPB.Objective.add`, `Cslib.Logic.PL.VeriPB.objuCheck`: the sum of
  objectives and the check of an objective update `obju`.
* `Cslib.Logic.PL.VeriPB.proj`, `Cslib.Logic.PL.VeriPB.exclusion`,
  `Cslib.Logic.PL.VeriPB.presFree`, `Cslib.Logic.PL.VeriPB.projections`: projections to the
  preserved set, the solution-excluding constraint of `solx`, witnesses that leave the preserved
  set alone, and the projected solutions that `ENUMERATION` counts.
* `Cslib.Logic.PL.VeriPB.sameVars`: two lists name the same set of variables (`epreserved` and
  `EQUIENUMERABLE`).
* `Cslib.Logic.PL.VeriPB.presChangeCheck`: the check of `preserved_add` and `preserved_rm`.
* `Cslib.Logic.PL.VeriPB.solsLE`, `Cslib.Logic.PL.VeriPB.InjInv`: the solutions of value at most
  a bound, and the counting injections between their projections.

## Main results

* `Cslib.Logic.PL.VeriPB.Witness.holds_substC`: `σ ⊨ D|ω` iff `σ ∘ ω ⊨ D`.
* `Cslib.Logic.PL.VeriPB.redCheck_sound`, `Cslib.Logic.PL.VeriPB.redCheckOn_sound`: a checked
  `red` step repairs a solution of the database without raising the objective.
* `Cslib.Logic.PL.VeriPB.Order.good_of_defCheck`, `Cslib.Logic.PL.VeriPB.LoadedOrder.isPreorder`,
  `Cslib.Logic.PL.VeriPB.LoadedOrder.wellFounded`: an accepted order is a specification and a
  preorder with a well founded strict part.
* `Cslib.Logic.PL.VeriPB.domCheck_sound`, `Cslib.Logic.PL.VeriPB.SatObjPo.dom`: soundness of
  `dom`; `Cslib.Logic.PL.VeriPB.stepTop_ordInv`: the order invariant.
* `Cslib.Logic.PL.VeriPB.objuCheck_sound`: a checked objective update keeps the objective's
  values on the solutions of the core set; `Cslib.Logic.PL.VeriPB.Objective.eval_add`: the value
  of a sum of objectives.
* `Cslib.Logic.PL.VeriPB.stepTop_inv`: the core invariant;
  `Cslib.Logic.PL.VeriPB.stepTop_fwd`, `Cslib.Logic.PL.VeriPB.stepTop_back`: what one step does to
  one solution; `Cslib.Logic.PL.VeriPB.stepTop_injInv`: the counting injections;
  `Cslib.Logic.PL.VeriPB.invariants_of_runTop`: all invariants after a run.
* `Cslib.Logic.PL.VeriPB.stepTop_mono`, `Cslib.Logic.PL.VeriPB.runTop_mono`: the monotonicity
  facts of a step and of a run.
* `Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_cnf_of_checkRed`: soundness for `UNSAT`.
* `Cslib.Logic.PL.VeriPB.exists_satisfies_of_checkRed`: soundness for `SAT`.
* `Cslib.Logic.PL.VeriPB.le_eval_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed_bounds`,
  `Cslib.Logic.PL.VeriPB.exists_eval_le_of_checkRed`: soundness for `BOUNDS`, its lower bound,
  infinite lower bound and upper bound.
* `Cslib.Logic.PL.VeriPB.holds_exclusion`: the solution-excluding constraint holds exactly off the
  logged projection.
* `Cslib.Logic.PL.VeriPB.presChangeCheck_sound`: a checked change of the preserved set gives
  `x ⇔ C` on the core set.
* `Cslib.Logic.PL.VeriPB.proj_eq_iff_of_presChangeCheck`: after a checked change of the
  preserved set, the projections of the core set's solutions to the old and to the new set
  determine each other.
* `Cslib.Logic.PL.VeriPB.isSome_of_checkRed_enum`,
  `Cslib.Logic.PL.VeriPB.le_encard_of_checkRed_enum`,
  `Cslib.Logic.PL.VeriPB.encard_eq_of_checkRed_enumComplete`: soundness for `ENUMERATION`.
* `Cslib.Logic.PL.VeriPB.checkRed_map_step`: without `red` and solutions, the checker of
  `Cslib.Logic.PL.VeriPB.check`.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

public section

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
@[expose]
def find (ω : Witness) (v : ℕ) : Option WVal := (ω.find? (·.1 == v)).map (·.2)

/-- The assignment `σ ∘ ω`: the value of `v` under `ω`, evaluated in `σ`. -/
@[expose]
def apply (σ : ℕ → Bool) (ω : Witness) (v : ℕ) : Bool :=
  match ω.find v with
  | none => σ v
  | some .zero => false
  | some .one => true
  | some (.lit l) => Literal.eval σ l

/-- A term under the witness: the terms it becomes and the constant it contributes. -/
@[expose]
def substTerm (ω : Witness) (t : ℕ × Literal ℕ) : List (ℕ × Literal ℕ) × ℕ :=
  match ω.find (termVar t) with
  | none => ([t], 0)
  | some .zero => ([], if termPos t then 0 else t.1)
  | some .one => ([], if termPos t then t.1 else 0)
  | some (.lit l) => ([(t.1, if termPos t then l else Std.Sat.Literal.negate l)], 0)

/-- **The constraint `D|ω`**: every term under the witness, constants moved into the degree. -/
@[expose]
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

/-! ### Orders -/

/-- The value of a witness entry under `σ`. -/
@[expose]
def WVal.eval (σ : ℕ → Bool) : WVal → Bool
  | .zero => false
  | .one => true
  | .lit l => Literal.eval σ l

/-- The assignment `d` with the variables `ks` given the values `bs`, the first occurrence of a
variable counting; variables past the end of `bs` keep their value under `d`. -/
@[expose]
def assignOn : List ℕ → List Bool → (ℕ → Bool) → ℕ → Bool
  | k :: ks, b :: bs, d, j => if j = k then b else assignOn ks bs d j
  | _, _, d, j => d j

private theorem assignOn_of_not_mem {ks : List ℕ} {j : ℕ} (h : j ∉ ks) (bs : List Bool)
    (d : ℕ → Bool) : assignOn ks bs d j = d j := by
  fun_induction assignOn ks bs d j with
  | case1 => exact absurd List.mem_cons_self h -- j = k
  | case2 k ks b bs d j hjk ih => exact ih (mt (List.mem_cons_of_mem k) h) -- j ≠ k: recurse
  | case3 => rfl -- a list is exhausted

private theorem assignOn_congr {ks : List ℕ} {bs : List Bool} {j : ℕ} (h : j ∈ ks)
    (hl : ks.length ≤ bs.length) (d d' : ℕ → Bool) : assignOn ks bs d j = assignOn ks bs d' j := by
  induction ks generalizing bs with
  | nil => simp at h
  | cons k ks ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [assignOn]
      split
      · rfl
      · rename_i hjk
        exact ih (by simpa [hjk] using h) (by simpa using hl)

private theorem map_assignOn_of_disjoint {ks js : List ℕ} (h : ∀ j ∈ js, j ∉ ks) (bs : List Bool)
    (d : ℕ → Bool) : js.map (assignOn ks bs d) = js.map d :=
  List.map_congr_left fun j hj => assignOn_of_not_mem (h j hj) bs d

private theorem map_assignOn {ks : List ℕ} {bs : List Bool} (hn : ks.Nodup)
    (hl : ks.length = bs.length) (d : ℕ → Bool) : ks.map (assignOn ks bs d) = bs := by
  induction ks generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons => simp at hl
  | cons k ks ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      rw [List.nodup_cons] at hn
      simp only [List.map_cons, assignOn, ite_true, List.cons.injEq, true_and]
      conv => rhs; rw [← ih (bs := bs) hn.2 (by simpa using hl)]
      refine List.map_congr_left fun j hj => ?_
      simp [show j ≠ k from fun h => hn.1 (h ▸ hj)]

namespace Witness

theorem apply_eq (σ : ℕ → Bool) (ω : Witness) (v : ℕ) :
    apply σ ω v = ((ω.find v).map (WVal.eval σ)).getD (σ v) := by
  unfold apply
  rcases ω.find v with _ | _ | _ | _ <;> rfl

theorem apply_nil (σ : ℕ → Bool) : apply σ [] = σ := by
  funext v
  simp [apply, find]

/-- A witness that starts with the pairs of `ks` and `vs` gives the variables `ks` the values of
`vs`. -/
private theorem apply_zip_append (σ : ℕ → Bool) (ks : List ℕ) (vs : List WVal) (ω : Witness) :
    apply σ (ks.zip vs ++ ω) = assignOn ks (vs.map (WVal.eval σ)) (apply σ ω) := by
  funext j
  induction ks generalizing vs with
  | nil => simp [assignOn]
  | cons k ks ih =>
    cases vs with
    | nil => simp [assignOn]
    | cons w vs =>
      simp only [List.zip_cons_cons, List.cons_append, List.map_cons, assignOn]
      rw [← ih, apply_eq, apply_eq]
      by_cases h : j = k
      · subst h; simp [find]
      · simp [find, Ne.symm h, h]

/-- The literal `l↾ω`: `l` under the witness. -/
def litVal (ω : Witness) (l : Literal ℕ) : WVal :=
  match ω.find l.1 with
  | none => .lit l
  | some .zero => if l.2 then .zero else .one
  | some .one => if l.2 then .one else .zero
  | some (.lit m) => .lit (if l.2 then m else Std.Sat.Literal.negate m)

theorem eval_litVal (σ : ℕ → Bool) (ω : Witness) (l : Literal ℕ) :
    (litVal ω l).eval σ = Literal.eval (apply σ ω) l := by
  obtain ⟨v, b⟩ := l
  simp only [litVal, Literal.eval, apply_eq]
  rcases ω.find v with _ | _ | _ | ⟨u, c⟩ <;> cases b <;>
    simp [WVal.eval, Literal.eval, Std.Sat.Literal.negate, not_beq_eq_beq_not]

end Witness

/-- The positive literals of the variables `xs`, as witness values. -/
private def posVals (xs : List ℕ) : List WVal := xs.map fun x => .lit (x, true)

private theorem map_eval_posVals (σ : ℕ → Bool) (xs : List ℕ) :
    (posVals xs).map (WVal.eval σ) = xs.map σ := by
  simp [posVals, Function.comp_def, WVal.eval, Literal.eval]

/-- A variable listed in `ks` gets the value of `f` under `assignOn ks (ks.map f)`. -/
private theorem assignOn_map_self {ks : List ℕ} {j : ℕ} (h : j ∈ ks) (f d : ℕ → Bool) :
    assignOn ks (ks.map f) d j = f j := by
  induction ks with
  | nil => simp at h
  | cons k ks ih =>
    simp only [List.map_cons, assignOn]
    split
    · next hjk => rw [hjk]
    · next hjk => exact ih (by simpa [hjk] using h)

/-- **Deciding `∃ ρ, |ρ| = n ∧ p ρ`** over lists of booleans, by trying the lists of length `n`. -/
@[expose]
def decExistsBools (p : List Bool → Prop) [DecidablePred p] :
    (n : ℕ) → Decidable (∃ ρ : List Bool, ρ.length = n ∧ p ρ)
  | 0 => decidable_of_iff (p [])
    ⟨fun h => ⟨[], rfl, h⟩, fun ⟨ρ, hρ, h⟩ => List.length_eq_zero_iff.1 hρ ▸ h⟩
  | n + 1 =>
    haveI := decExistsBools (fun ρ => p (false :: ρ) ∨ p (true :: ρ)) n
    decidable_of_iff (∃ ρ : List Bool, ρ.length = n ∧ (p (false :: ρ) ∨ p (true :: ρ)))
      ⟨fun ⟨ρ, hρ, h⟩ => h.elim (fun h => ⟨_, by simp [hρ], h⟩) fun h => ⟨_, by simp [hρ], h⟩,
        fun ⟨ρ, hρ, h⟩ => by
          match ρ, hρ with
          | false :: ρ, hρ => exact ⟨ρ, by simpa using hρ, .inl h⟩
          | true :: ρ, hρ => exact ⟨ρ, by simpa using hρ, .inr h⟩⟩

/-- **An order** `O⪯(u, v, a)` defined by `def_order` (§5.3): the left variables `u`, the right
variables `v`, the auxiliary variables `a`, the constraints of its specification `S⪯(u, v, a)`
and those of its definition `O⪯(u, v, a)`. It relates `x ⪯ y`
(`Cslib.Logic.PL.VeriPB.Order.Le`) when, for some values of `a`, the specification and the
definition hold with `u` taking the values `x` and `v` the values `y` (§5.4). An order without
auxiliary variables has an empty specification, and then `x ⪯ y` when the definition holds. -/
structure Order where
  /-- The left variables `u`. -/
  left : List ℕ
  /-- The right variables `v`. -/
  right : List ℕ
  /-- The auxiliary variables `a`. -/
  aux : List ℕ
  /-- The constraints `S⪯(u, v, a)` of the specification. -/
  spec : List PBConstr
  /-- The constraints `O⪯(u, v, a)` of the definition. -/
  defn : List PBConstr
  deriving DecidableEq, Repr

namespace Order

/-- The variables `u`, `v` and `a`. -/
@[expose]
def vars (O : Order) : List ℕ := O.left ++ O.right ++ O.aux

/-- The assignment giving `u` the values `x`, `v` the values `y`, `a` the values `ρ`, and every
other variable `false`. -/
@[expose]
def inst (O : Order) (x y ρ : List Bool) : ℕ → Bool :=
  assignOn O.left x (assignOn O.right y (assignOn O.aux ρ fun _ => false))

/-- **The relation of an order on value vectors** (§5.4): `x ⪯ y` when some values `ρ` of the
auxiliary variables satisfy `S⪯(x, y, ρ) ∧ O⪯(x, y, ρ)`, that is, every constraint of the
specification and of the definition holds with `u` taking the values `x`, `v` the values `y` and
`a` the values `ρ`. -/
@[expose]
def Le (O : Order) (x y : List Bool) : Prop :=
  ∃ ρ : List Bool, ρ.length = O.aux.length ∧ ∀ D ∈ O.spec ++ O.defn, D.Holds (O.inst x y ρ)

instance (O : Order) (x y : List Bool) : Decidable (O.Le x y) :=
  decExistsBools (fun ρ => ∀ D ∈ O.spec ++ O.defn, D.Holds (O.inst x y ρ)) O.aux.length

/-- The syntactic conditions of CakePB's `check_good_aord`: `u` and `v` have the same length,
`u`, `v` and `a` are distinct variables, and the specification and the definition use no
others. -/
@[expose]
def wellFormed (O : Order) : Bool :=
  O.left.length == O.right.length && decide O.vars.Nodup &&
    (O.spec ++ O.defn).all fun D => D.terms.all fun t => O.vars.contains (termVar t)

/-- The substitution of `u` by the values `a`, of `v` by `b`, and of the auxiliary variables by
`r`. -/
def subst (O : Order) (a b r : List WVal) : Witness :=
  O.left.zip a ++ (O.right.zip b ++ O.aux.zip r)

/-- The specification instantiated with `u` replaced by `a`, `v` by `b` and the auxiliary
variables by `r`, such as `S⪯(z↾ω, z, a)` (`Cslib.Logic.PL.VeriPB.Order.holds_specC`). -/
def specC (O : Order) (a b r : List WVal) : List PBConstr :=
  O.spec.map (Witness.substC (O.subst a b r))

/-- The definition instantiated with `u` replaced by `a`, `v` by `b` and the auxiliary variables
by `r`, such as `O⪯(z↾ω, z, a)` (`Cslib.Logic.PL.VeriPB.Order.holds_instC`). -/
def instC (O : Order) (a b r : List WVal) : List PBConstr :=
  O.defn.map (Witness.substC (O.subst a b r))

/-- **A good order**: well formed, a specification (CakePB's `is_spec`: for all values of `u`
and `v`, some values of `a` satisfy it), and reflexive and transitive on the vectors as long as
`u`. `def_order` checks this (`Cslib.Logic.PL.VeriPB.Order.good_of_defCheck`). -/
structure Good (O : Order) : Prop where
  wf : O.wellFormed = true
  spec : ∀ x y : List Bool, ∃ ρ : List Bool, ρ.length = O.aux.length ∧
    ∀ S ∈ O.spec, S.Holds (O.inst x y ρ)
  refl : ∀ x : List Bool, x.length = O.left.length → O.Le x x
  trans : ∀ x y w : List Bool, x.length = O.left.length → y.length = O.left.length →
    w.length = O.left.length → O.Le x y → O.Le y w → O.Le x w

theorem wellFormed_iff {O : Order} : O.wellFormed = true ↔ O.left.length = O.right.length ∧
    O.vars.Nodup ∧ ∀ D ∈ O.spec ++ O.defn, ∀ t ∈ D.terms, termVar t ∈ O.vars := by
  simp only [wellFormed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem, and_assoc]

/-- The auxiliary variables of a good order are distinct. -/
theorem Good.aux_nodup {O : Order} (h : O.Good) : O.aux.Nodup :=
  (List.nodup_append.1 (wellFormed_iff.1 h.wf).2.1).2.1

private theorem holds_subst {O : Order} (hwf : O.wellFormed = true) {a b r : List WVal}
    (ha : a.length = O.left.length) (hb : b.length = O.right.length)
    (hr : r.length = O.aux.length) (σ : ℕ → Bool) {D : PBConstr} (hD : D ∈ O.spec ++ O.defn) :
    (Witness.substC (O.subst a b r) D).Holds σ ↔
      D.Holds (O.inst (a.map (WVal.eval σ)) (b.map (WVal.eval σ)) (r.map (WVal.eval σ))) := by
  rw [Witness.holds_substC, subst, Witness.apply_zip_append, Witness.apply_zip_append,
    ← List.append_nil (O.aux.zip r), Witness.apply_zip_append, Witness.apply_nil]
  refine holds_congr fun t ht => ?_
  unfold inst
  have hv := (wellFormed_iff.1 hwf).2.2 D hD t ht
  simp only [vars, List.mem_append] at hv
  by_cases hl : termVar t ∈ O.left
  · exact assignOn_congr hl (by simp [ha]) _ _
  rw [assignOn_of_not_mem hl, assignOn_of_not_mem hl]
  by_cases hr' : termVar t ∈ O.right
  · exact assignOn_congr hr' (by simp [hb]) _ _
  rw [assignOn_of_not_mem hr', assignOn_of_not_mem hr']
  exact assignOn_congr (by tauto) (by simp [hr]) _ _

/-- **An instantiated specification** holds at `σ` exactly when the specification holds at the
values of `a`, `b` and `r` under `σ`. -/
theorem holds_specC {O : Order} (hwf : O.wellFormed = true) {a b r : List WVal}
    (ha : a.length = O.left.length) (hb : b.length = O.right.length)
    (hr : r.length = O.aux.length) (σ : ℕ → Bool) :
    (∀ G ∈ O.specC a b r, G.Holds σ) ↔ ∀ S ∈ O.spec,
      S.Holds (O.inst (a.map (WVal.eval σ)) (b.map (WVal.eval σ)) (r.map (WVal.eval σ))) := by
  simp only [specC, List.forall_mem_map]
  exact forall₂_congr fun D hD => holds_subst hwf ha hb hr σ (List.mem_append_left _ hD)

/-- **An instantiated definition** holds at `σ` exactly when the definition holds at the values
of `a`, `b` and `r` under `σ`. -/
theorem holds_instC {O : Order} (hwf : O.wellFormed = true) {a b r : List WVal}
    (ha : a.length = O.left.length) (hb : b.length = O.right.length)
    (hr : r.length = O.aux.length) (σ : ℕ → Bool) :
    (∀ G ∈ O.instC a b r, G.Holds σ) ↔ ∀ D ∈ O.defn,
      D.Holds (O.inst (a.map (WVal.eval σ)) (b.map (WVal.eval σ)) (r.map (WVal.eval σ))) := by
  simp only [instC, List.forall_mem_map]
  exact forall₂_congr fun D hD => holds_subst hwf ha hb hr σ (List.mem_append_right _ hD)

/-- The auxiliary variables do not occur in `c`. -/
def avoids (O : Order) (c : PBConstr) : Bool := c.terms.all fun t => !O.aux.contains (termVar t)

/-- A constraint without auxiliary variables does not see their values. -/
private theorem holds_iff_of_avoids {O : Order} {c : PBConstr} (h : O.avoids c = true)
    {σ σ' : ℕ → Bool} (hag : ∀ v ∉ O.aux, σ' v = σ v) : c.Holds σ' ↔ c.Holds σ :=
  holds_congr fun t ht => hag _ (by simpa using List.all_eq_true.1 h t ht)

end Order

/-- **A loaded order** (`load_order`, §5.3): an order with the literals `z` it is applied to. It
relates the assignments `α ⪯ β` when `z↾α ⪯ z↾β` (§5.4). -/
structure LoadedOrder where
  /-- The order. -/
  order : Order
  /-- The literals `z`. -/
  lits : List (Literal ℕ)
  deriving DecidableEq, Repr

namespace LoadedOrder

/-- The values `z↾σ` of the literals. -/
@[expose]
def vals (L : LoadedOrder) (σ : ℕ → Bool) : List Bool := L.lits.map (Literal.eval σ)

/-- **The relation of a loaded order on assignments**: `σ ⪯ τ` when `z↾σ ⪯ z↾τ`. -/
@[expose]
def Le (L : LoadedOrder) (σ τ : ℕ → Bool) : Prop := L.order.Le (L.vals σ) (L.vals τ)

/-- A good order loaded over as many literals as it has left variables, none of them on an
auxiliary variable, as CakePB's `guard_ord_t` requires. -/
structure Good (L : LoadedOrder) : Prop where
  order : L.order.Good
  length : L.lits.length = L.order.left.length
  lits_aux : ∀ l ∈ L.lits, l.1 ∉ L.order.aux

/-- The order goals `O⪯(z↾ω, z, a)` of `red` and `dom` (§5.4). With `S⪯(z↾ω, z, a)` they give
`σ ∘ ω ⪯ σ` (`Cslib.Logic.PL.VeriPB.LoadedOrder.le_apply_of_holds`). -/
def leGoals (L : LoadedOrder) (ω : Witness) : List PBConstr :=
  L.order.instC (L.lits.map (Witness.litVal ω)) (L.lits.map .lit) (posVals L.order.aux)

/-- The specification `S⪯(z↾ω, z, a)`, the premises of the scope `scope leq` (§5.4). -/
def leSpec (L : LoadedOrder) (ω : Witness) : List PBConstr :=
  L.order.specC (L.lits.map (Witness.litVal ω)) (L.lits.map .lit) (posVals L.order.aux)

/-- The constraints `O⪯(z, z↾ω, a)` that goal `#N + 1` of `dom` refutes (§5.4.2). -/
def geGoals (L : LoadedOrder) (ω : Witness) : List PBConstr :=
  L.order.instC (L.lits.map .lit) (L.lits.map (Witness.litVal ω)) (posVals L.order.aux)

/-- The specification `S⪯(z, z↾ω, a)`, the premises of the scope `scope geq` (§5.4.2). -/
def geSpec (L : LoadedOrder) (ω : Witness) : List PBConstr :=
  L.order.specC (L.lits.map .lit) (L.lits.map (Witness.litVal ω)) (posVals L.order.aux)

/-- The witness leaves the variables of `z` alone (§5.5.1, item 1c). -/
def untouched (L : LoadedOrder) (ω : Witness) : Bool := L.lits.all fun l => (ω.find l.1).isNone

theorem Good.le_refl {L : LoadedOrder} (hL : L.Good) (σ : ℕ → Bool) : L.Le σ σ :=
  hL.order.refl _ (by simp [vals, hL.length])

theorem Good.le_trans {L : LoadedOrder} (hL : L.Good) {σ τ ρ : ℕ → Bool} (h₁ : L.Le σ τ)
    (h₂ : L.Le τ ρ) : L.Le σ ρ :=
  hL.order.trans _ _ _ (by simp [vals, hL.length]) (by simp [vals, hL.length])
    (by simp [vals, hL.length]) h₁ h₂

/-- **A good loaded order is a preorder** on assignments. -/
theorem isPreorder {L : LoadedOrder} (hL : L.Good) : IsPreorder (ℕ → Bool) L.Le where
  refl := hL.le_refl
  trans _ _ _ := hL.le_trans

private theorem map_eval_lit (σ : ℕ → Bool) (ls : List (Literal ℕ)) :
    (ls.map WVal.lit).map (WVal.eval σ) = ls.map (Literal.eval σ) := by
  simp [Function.comp_def, WVal.eval]

private theorem map_eval_litVal (σ : ℕ → Bool) (ω : Witness) (ls : List (Literal ℕ)) :
    (ls.map (Witness.litVal ω)).map (WVal.eval σ) = ls.map (Literal.eval (Witness.apply σ ω)) := by
  simp [Function.comp_def, Witness.eval_litVal]

private theorem lengths {L : LoadedOrder} (hL : L.Good) (ω : Witness) :
    (L.lits.map (Witness.litVal ω)).length = L.order.left.length ∧
      (L.lits.map WVal.lit).length = L.order.right.length ∧
      (L.lits.map WVal.lit).length = L.order.left.length ∧
      (L.lits.map (Witness.litVal ω)).length = L.order.right.length ∧
      (posVals L.order.aux).length = L.order.aux.length := by
  have h := (Order.wellFormed_iff.1 hL.order.wf).1
  simp [hL.length, h, posVals]

private theorem holds_leSpec {L : LoadedOrder} (hL : L.Good) (ω : Witness) (σ : ℕ → Bool) :
    (∀ G ∈ L.leSpec ω, G.Holds σ) ↔ ∀ S ∈ L.order.spec,
      S.Holds (L.order.inst (L.vals (Witness.apply σ ω)) (L.vals σ) (L.order.aux.map σ)) := by
  obtain ⟨h₁, h₂, -, -, h₅⟩ := lengths hL ω
  rw [leSpec, Order.holds_specC hL.order.wf h₁ h₂ h₅, map_eval_lit, map_eval_litVal,
    map_eval_posVals]
  rfl

private theorem holds_leGoals {L : LoadedOrder} (hL : L.Good) (ω : Witness) (σ : ℕ → Bool) :
    (∀ G ∈ L.leGoals ω, G.Holds σ) ↔ ∀ D ∈ L.order.defn,
      D.Holds (L.order.inst (L.vals (Witness.apply σ ω)) (L.vals σ) (L.order.aux.map σ)) := by
  obtain ⟨h₁, h₂, -, -, h₅⟩ := lengths hL ω
  rw [leGoals, Order.holds_instC hL.order.wf h₁ h₂ h₅, map_eval_lit, map_eval_litVal,
    map_eval_posVals]
  rfl

private theorem holds_geSpec {L : LoadedOrder} (hL : L.Good) (ω : Witness) (σ : ℕ → Bool) :
    (∀ G ∈ L.geSpec ω, G.Holds σ) ↔ ∀ S ∈ L.order.spec,
      S.Holds (L.order.inst (L.vals σ) (L.vals (Witness.apply σ ω)) (L.order.aux.map σ)) := by
  obtain ⟨-, -, h₃, h₄, h₅⟩ := lengths hL ω
  rw [geSpec, Order.holds_specC hL.order.wf h₃ h₄ h₅, map_eval_lit, map_eval_litVal,
    map_eval_posVals]
  rfl

private theorem holds_geGoals {L : LoadedOrder} (hL : L.Good) (ω : Witness) (σ : ℕ → Bool) :
    (∀ G ∈ L.geGoals ω, G.Holds σ) ↔ ∀ D ∈ L.order.defn,
      D.Holds (L.order.inst (L.vals σ) (L.vals (Witness.apply σ ω)) (L.order.aux.map σ)) := by
  obtain ⟨-, -, h₃, h₄, h₅⟩ := lengths hL ω
  rw [geGoals, Order.holds_instC hL.order.wf h₃ h₄ h₅, map_eval_lit, map_eval_litVal,
    map_eval_posVals]
  rfl

/-- **The order goals** with their specification give `σ ∘ ω ⪯ σ`, the values of the auxiliary
variables at `σ` witnessing it. -/
theorem le_apply_of_holds {L : LoadedOrder} (hL : L.Good) {ω : Witness} {σ : ℕ → Bool}
    (hs : ∀ G ∈ L.leSpec ω, G.Holds σ) (hg : ∀ G ∈ L.leGoals ω, G.Holds σ) :
    L.Le (Witness.apply σ ω) σ :=
  ⟨L.order.aux.map σ, by simp, List.forall_mem_append.2
    ⟨(holds_leSpec hL ω σ).1 hs, (holds_leGoals hL ω σ).1 hg⟩⟩

/-- The witness gives no variable a literal on an auxiliary variable of the order (part of
CakePB's `fresh_aux`). -/
def imageAvoids (L : LoadedOrder) (ω : Witness) : Bool :=
  ω.all fun e => match e.2 with
    | .lit l => !L.order.aux.contains l.1
    | _ => true

private theorem find_mem {ω : Witness} {v : ℕ} {w : WVal} (h : ω.find v = some w) :
    ∃ e ∈ ω, e.2 = w := by
  simp only [Witness.find, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, List.mem_of_find?_eq_some he, rfl⟩

/-- Off the auxiliary variables, `σ ∘ ω` depends only on `σ` off them, if `ω` gives no variable
a literal on them. -/
private theorem apply_agree {L : LoadedOrder} {ω : Witness} (hω : L.imageAvoids ω = true)
    {σ σ' : ℕ → Bool} (hag : ∀ v ∉ L.order.aux, σ' v = σ v) (v : ℕ) (hv : v ∉ L.order.aux) :
    Witness.apply σ' ω v = Witness.apply σ ω v := by
  rw [Witness.apply_eq, Witness.apply_eq]
  cases hf : ω.find v with
  | none => simp [hag v hv]
  | some w =>
    obtain ⟨e, he, rfl⟩ := find_mem hf
    have := List.all_eq_true.1 hω e he
    cases h : e.2 with
    | zero => rfl
    | one => rfl
    | lit l =>
      rw [h] at this
      have hl : l.1 ∉ L.order.aux := by simpa using this
      simp only [Option.map_some, Option.getD_some, WVal.eval, Literal.eval, hag _ hl]

private theorem vals_agree {L : LoadedOrder} (hL : L.Good) {σ σ' : ℕ → Bool}
    (hag : ∀ v ∉ L.order.aux, σ' v = σ v) : L.vals σ' = L.vals σ :=
  List.map_congr_left fun l hl => by simp [Literal.eval, hag _ (hL.lits_aux l hl)]

private theorem vals_apply_agree {L : LoadedOrder} (hL : L.Good) {ω : Witness}
    (hω : L.imageAvoids ω = true) {σ σ' : ℕ → Bool} (hag : ∀ v ∉ L.order.aux, σ' v = σ v) :
    L.vals (Witness.apply σ' ω) = L.vals (Witness.apply σ ω) :=
  vals_agree hL (apply_agree hω hag)

/-- **The specification of the order goals is satisfiable**: some values of the auxiliary
variables, given to `σ`, satisfy `S⪯(z↾ω, z, a)`. -/
theorem exists_leSpec {L : LoadedOrder} (hL : L.Good) {ω : Witness}
    (hω : L.imageAvoids ω = true) (σ : ℕ → Bool) :
    ∃ ρ : List Bool, ρ.length = L.order.aux.length ∧
      ∀ G ∈ L.leSpec ω, G.Holds (assignOn L.order.aux ρ σ) := by
  obtain ⟨ρ, hρ, hS⟩ := hL.order.spec (L.vals (Witness.apply σ ω)) (L.vals σ)
  have hag : ∀ v ∉ L.order.aux, assignOn L.order.aux ρ σ v = σ v := fun v hv =>
    assignOn_of_not_mem hv ρ σ
  have hnd := hL.order.aux_nodup
  refine ⟨ρ, hρ, (holds_leSpec hL ω _).2 ?_⟩
  rw [vals_apply_agree hL hω hag, vals_agree hL hag, map_assignOn hnd hρ.symm]
  exact hS

/-- **The negated order goal, semantically**: if `σ ⪯ σ ∘ ω`, some values of the auxiliary
variables, given to `σ`, satisfy `S⪯(z, z↾ω, a)` and `O⪯(z, z↾ω, a)`. -/
theorem exists_ge_of_le {L : LoadedOrder} (hL : L.Good) {ω : Witness}
    (hω : L.imageAvoids ω = true) {σ : ℕ → Bool} (h : L.Le σ (Witness.apply σ ω)) :
    ∃ ρ : List Bool, ρ.length = L.order.aux.length ∧
      ∀ G ∈ L.geSpec ω ++ L.geGoals ω, G.Holds (assignOn L.order.aux ρ σ) := by
  obtain ⟨ρ, hρ, hSO⟩ := h
  have hag : ∀ v ∉ L.order.aux, assignOn L.order.aux ρ σ v = σ v := fun v hv =>
    assignOn_of_not_mem hv ρ σ
  have hnd := hL.order.aux_nodup
  refine ⟨ρ, hρ, List.forall_mem_append.2 ⟨(holds_geSpec hL ω _).2 ?_, (holds_geGoals hL ω _).2 ?_⟩⟩
  all_goals
    rw [vals_apply_agree hL hω hag, vals_agree hL hag, map_assignOn hnd hρ.symm]
    intro D hD
  · exact hSO D (List.mem_append_left _ hD)
  · exact hSO D (List.mem_append_right _ hD)

private theorem vals_apply_of_untouched {L : LoadedOrder} {ω : Witness} (h : L.untouched ω = true)
    (σ : ℕ → Bool) : L.vals (Witness.apply σ ω) = L.vals σ := by
  simp only [untouched, List.all_eq_true, Option.isNone_iff_eq_none] at h
  simp only [vals]
  refine List.map_congr_left fun l hl => ?_
  simp [Literal.eval, Witness.apply_eq, h l hl]

/-- **The strict part of a good loaded order is well founded**: the order depends only on the
values of the finitely many literals `z`. -/
theorem wellFounded {L : LoadedOrder} (hL : L.Good) :
    WellFounded fun σ τ : ℕ → Bool => L.Le σ τ ∧ ¬ L.Le τ σ := by
  have hg := hL.order
  let r : List.Vector Bool L.order.left.length → List.Vector Bool L.order.left.length → Prop :=
    fun a b => L.order.Le a.1 b.1 ∧ ¬ L.order.Le b.1 a.1
  have : IsTrans _ r := ⟨fun a b c hab hbc =>
    ⟨hg.trans _ _ _ a.2 b.2 c.2 hab.1 hbc.1,
      fun hca => hab.2 (hg.trans _ _ _ b.2 c.2 a.2 hbc.1 hca)⟩⟩
  have : Std.Irrefl r := ⟨fun a h => h.2 h.1⟩
  exact InvImage.wf (fun σ => (⟨L.vals σ, by simp [vals, hL.length]⟩ :
    List.Vector Bool L.order.left.length)) (Finite.wellFounded_of_trans_of_irrefl r)

end LoadedOrder

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
@[expose]
def eval (f : Objective) (σ : ℕ → Bool) : ℤ := linVal σ f.lin + f.const

/-- The constraint `f ≥ b`. -/
@[expose]
def atLeast (f : Objective) (b : ℤ) : PBConstr := fromLinear f.lin (b - f.const)

theorem holds_atLeast (σ : ℕ → Bool) (f : Objective) (b : ℤ) :
    (f.atLeast b).Holds σ ↔ b ≤ f.eval σ := by
  rw [atLeast, holds_fromLinear_iff, eval]
  omega

/-- **The objective-improving constraint** `f ≤ u - 1` (equation (3.6) of the documentation). -/
@[expose]
def improving (f : Objective) (u : ℤ) : PBConstr :=
  fromLinear (f.lin.map fun e => (e.1, -e.2)) (f.const - u + 1)

theorem holds_improving (σ : ℕ → Bool) (f : Objective) (u : ℤ) :
    (f.improving u).Holds σ ↔ f.eval σ < u := by
  rw [improving, holds_fromLinear_iff, linVal_map_neg, eval]
  omega

end Objective

/-- The value of an optional objective: a decision problem has the trivial objective `0` (§5 of
the documentation). -/
@[expose]
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

/-- A proof goal label of a subproof: `#k`, or a constraint of the database by number. For an
order of `N` constraints (§5.4), the goals of `red` are `#1`, the constraint `C|ω` itself,
`#2` … `#N + 1`, the order goals, and `#N + 2`, the objective goal; those of `dom` are `#1` …
`#N`, the order goals, `#N + 1`, the negated order, and `#N + 2`, the objective goal. Those of
the transitivity and reflexivity proofs of an order are its constraints (§5.3), and those of
`obju` are `#1` and `#2` (§5.9). -/
inductive GoalId where
  /-- `#k`. -/
  | hash (k : ℕ)
  /-- The goal `D|ω` of the database constraint with this number. -/
  | db (n : ℕ)
  deriving DecidableEq, Repr

/-- An item of the subproof of a `red` step: a derivation step, which may use `¬C`, or a
`proofgoal` block, which starts from the negation of its goal and must derive the contradiction
it names. -/
inductive RedItem where
  /-- A derivation step. -/
  | step (s : Step)
  /-- `proofgoal g … qed : n`: its premises, the negation of the goal or, for the negated order
of `dom`, the constraints to refute, take the next numbers, and the steps must derive the
contradiction `n`. -/
  | goal (g : GoalId) (sub : List Step) (qed : ℕ)
  /-- `scope leq … end scope;` (`geq = false`) or `scope geq … end scope;` (`geq = true`), in
  a subproof of `red` or `dom` with an order loaded (§5.4.1, §5.4.2): the specification
  `S⪯(z↾ω, z, a)`, or `S⪯(z, z↾ω, a)`, takes the next numbers, the items run, and the scope's
  constraints are dropped after it; only the numbering advances. Scopes do not nest. -/
  | scope (geq : Bool) (items : List RedItem)
  deriving Repr

/-- The item is a scope. -/
def RedItem.isScope : RedItem → Bool
  | .scope .. => true
  | _ => false

/-- A proof of the transitivity or the reflexivity of an order (§5.3): its items, whose `#k`
goals are the constraints of the order, and an optional closing contradiction. -/
structure OrderProof where
  /-- The items. -/
  items : List RedItem
  /-- The closing contradiction, if any. -/
  qed : Option ℕ
  deriving Repr

/-- The justification of a constraint `C` of the specification of an order (§5.3): a `red` step
`red C : ω [: subproof … qed [: n]]` from the constraints before it, with `none` for no subproof.
The witness may set only auxiliary variables. -/
structure SpecStep where
  /-- The witness `ω`. -/
  witness : Witness
  /-- The subproof, if any. -/
  sub : Option (List RedItem)
  /-- The closing contradiction, if any. -/
  qed : Option ℕ
  deriving Repr

/-- The fresh variables of a transitivity proof (§5.3): `fresh_right w`, as long as the left
variables, and `fresh_aux_1 b` and `fresh_aux_2 c`, as long as the auxiliary variables. -/
structure TransVars where
  /-- The fresh right variables `w`. -/
  right : List ℕ
  /-- The fresh auxiliary variables `b` of `S⪯(v, w, b)` and `O⪯(v, w, b)`. -/
  aux₁ : List ℕ
  /-- The fresh auxiliary variables `c` of `S⪯(u, w, c)` and `O⪯(u, w, c)`. -/
  aux₂ : List ℕ
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
  /-- `def_order name …` (§5.3): define the order `O` under this name, with the derivation of its
  specification, the fresh variables and the proof of its transitivity, and the proof of its
  reflexivity. -/
  | defOrder (name : String) (O : Order) (spec : List SpecStep) (fresh : TransVars)
      (trans refl : OrderProof)
  /-- `load_order name z`: load the order of this name over the literals `z`, moving every
  constraint to the core set (§5.3). -/
  | loadOrder (name : String) (z : List (Literal ℕ))
  /-- `load_order;` without arguments: unload the order (§5.3), also when none is loaded, as in
  VeriPB (CakePB rejects that case). -/
  | unloadOrder
  /-- `dom C : ω [: subproof … qed [: n]]`, with `none` for no subproof (§5.4.2), numbered as
  `red`. -/
  | dom (c : PBConstr) (ω : Witness) (sub : Option (List RedItem)) (qed : Option ℕ)
  /-- `eord_def name …` (§5.11.3): the order of this name has exactly the variables of `O`, in
  order, and its specification and definition are those of `O`, in order, up to normalization
  and the order of terms. -/
  | eordDef (name : String) (O : Order)
  /-- `eord_loaded name z` (§5.11.3): the loaded order is the one of this name, over the literals
  `z`, in order. -/
  | eordLoaded (name : String) (z : List (Literal ℕ))
  /-- `preserved_add x : C` (`add = true`) or `preserved_rm x : C` (`add = false`), with an
  optional subproof of the goals `#1`, `x ⇒ C`, and `#2`, `x ⇐ C` (§5.10): add `x` to the
  preserved set, or remove it. -/
  | presChange (add : Bool) (x : ℕ) (c : PBConstr) (sub : Option (List RedItem))
  /-- `epreserved P` (§5.11.4): the preserved set is `P`, as a set of variables. -/
  | epreserved (vars : List ℕ)
  /-- `e C : j` (§5.11.1): the constraint numbered `j` is `C` after normalization, up to the order
  of terms. Like the other checks of §5.11, it changes nothing. -/
  | econstr (c : PBConstr) (j : ℕ)
  deriving Repr

/-- The linear form `L - L'`: `L` with the coefficients of `L'` subtracted. -/
def subLinear (L L' : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  L'.foldr (fun e L => insertCoeff e.1 (-e.2) L) L

/-- **The objective goal** `f|ω ≤ f` of a `red` step (§5.4.1 of the documentation), as the
constraint `∑ᵥ wᵥ xᵥ - (f|ω - k') ≥ k'`, with `k'` the constant that `ω` moves out of `f`. -/
def objGoal (f : Objective) (ω : Witness) : PBConstr :=
  fromLinear (subLinear f.lin (Witness.substLin ω f.lin).1) (Witness.substLin ω f.lin).2

/-- The entry `#k` of a list of goals, numbered from `1`. -/
private def hashAt {α : Type} (l : List α) : ℕ → Option α
  | 0 => none
  | k + 1 => l[k]?

/-- The `#` goals of `red C : ω` (§5.4.1): `C|ω`, the order goals `O⪯(z↾ω, z)` of the loaded
order, if any, and the objective goal `f|ω ≤ f`, if there is an objective. -/
def redHashGoals (obj : Option Objective) (ord : Option LoadedOrder) (ω : Witness)
    (c : PBConstr) : List PBConstr :=
  Witness.substC ω c :: ((ord.map (·.leGoals ω)).getD [] ++ (obj.map (objGoal · ω)).toList)

/-- The premises of a `proofgoal` block for the goal `G` to prove: its negation. -/
def negGoal (G : PBConstr) : List PBConstr := [G.negate]

/-- The premises of the `proofgoal` blocks of `red C : ω`: the negations of `#k` and of `D|ω`,
with `D` looked up in the database `db₀` of the step. -/
private def goalOf (obj : Option Objective) (ord : Option LoadedOrder) (db₀ : List (ℕ × PBConstr))
    (ω : Witness) (c : PBConstr) : GoalId → Option (List PBConstr)
  | .hash k => (hashAt (redHashGoals obj ord ω c) k).map negGoal
  | .db n => (lookup db₀ n).map fun D => negGoal (Witness.substC ω D)

/-- Add the constraints `ps` to the database, numbered from `n`. -/
private def pushAll : List (ℕ × PBConstr) → ℕ → List PBConstr → List (ℕ × PBConstr) × ℕ
  | db, n, [] => (db, n)
  | db, n, p :: ps => pushAll ((n, p) :: db) (n + 1) ps

/-- A refuted premise list of a subproof, tagged with the scope it was refuted in: `none` outside
the scopes, `some false` in `scope leq` and `some true` in `scope geq`. -/
private abbrev Tagged := Option Bool × List PBConstr

mutual

/-- Run one item of a subproof (`Cslib.Logic.PL.VeriPB.runGoals`) in the scope `cur`: a step, a
`proofgoal` block, whose premise list is recorded with the tag `cur` once it is refuted, or a
scope, allowed only outside the scopes. -/
private def runItem (goal : GoalId → Option (List PBConstr)) :
    (Bool → Option (List PBConstr)) → Option Bool → List (ℕ × PBConstr) → ℕ → RedItem →
      List Tagged → Option (List (ℕ × PBConstr) × ℕ × List Tagged)
  | _, _, db, n, .step s, proved => (runStep db n s).map fun (db', n') => (db', n', proved)
  | _, cur, db, n, .goal g sub q, proved =>
    match goal g with
    | none => none
    | some ps =>
      match runSteps (pushAll db n ps).1 (pushAll db n ps).2 sub with
      | some (db', n') => if namesContra db' q then some (db, n', (cur, ps) :: proved) else none
      | none => none
  | scope, cur, db, n, .scope b inner, proved =>
    if cur.isNone then
      match scope b with
      | none => none
      | some S =>
        match runGoals goal scope (some b) (pushAll db n S).1 (pushAll db n S).2 inner proved with
        | some (_, n', proved') => some (db, n', proved')
        | none => none
    else none

/-- Run the items of a subproof in the scope `cur` (`none` at its top), whose goal labels name the
premises `goal` of their `proofgoal` blocks, collecting the premise lists that the blocks refute,
tagged with their scope, as CakePB's `extract_scoped_pids` keeps the scope of each proof goal. A
block's constraints are dropped after it; only the numbering advances. A scope `scope leq`
(`false`) or `scope geq` (`true`) adds the premises `scope b`, if it is allowed; its constraints
are dropped after it, and scopes do not nest. -/
private def runGoals (goal : GoalId → Option (List PBConstr)) :
    (Bool → Option (List PBConstr)) → Option Bool → List (ℕ × PBConstr) → ℕ → List RedItem →
      List Tagged → Option (List (ℕ × PBConstr) × ℕ × List Tagged)
  | _, _, db, n, [], proved => some (db, n, proved)
  | scope, cur, db, n, it :: items, proved =>
    match runItem goal scope cur db n it proved with
    | some (db', n', proved') => runGoals goal scope cur db' n' items proved'
    | none => none

end

/-- The premise lists refuted outside the scopes or in the scope `b`: those that count for a goal
proved there (CakePB's `extract_scoped_pids` and `find_scope_1`). -/
private def visible (b : Bool) (proved : List Tagged) : List (List PBConstr) :=
  (proved.filter fun e => e.1.all (· == b)).map (·.2)

/-- No scopes: `scope` allows none. -/
private def noScope : Bool → Option (List PBConstr) := fun _ => none

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
constraint of `core` up to the order of terms, or a `proofgoal` block refuted its negation. -/
private def objuCovered (core : List (ℕ × PBConstr)) (proved : List (List PBConstr))
    (G : PBConstr) : Bool :=
  G.normalize.degree == 0 || core.any (fun e => sameUpToOrder e.2 G.normalize) ||
    proved.contains (negGoal G)

/-- A goal constraint `G` needs no subproof, given the negation `negC` of the constraint being
added: it is covered as a goal of `obju` with the database `db₀`
(`Cslib.Logic.PL.VeriPB.objuCovered`), or `negC` weakly syntactically implies it. -/
private def goalCovered (db₀ : List (ℕ × PBConstr)) (proved : List (List PBConstr))
    (negC G : PBConstr) : Bool :=
  objuCovered db₀ proved G || weakImplies negC G

/-- The goals that `red` and `dom` share, given the premises `db₀` and the refuted premise lists
`proved`: the objective goal `f|ω ≤ f` is covered, and so is `D|ω` for every constraint `D` of
`gs`, also when `ω` sets every literal of `D` it touches true or `D` weakly syntactically implies
`D|ω` (§5.5.1, items 2a–2f). -/
private def substCovered (obj : Option Objective) (db₀ gs : List (ℕ × PBConstr)) (ω : Witness)
    (c : PBConstr) (proved : List (List PBConstr)) : Bool :=
  obj.all (fun f => goalCovered db₀ proved c.negate (objGoal f ω)) &&
    gs.all fun e => Witness.touchedTrue ω e.2 || weakImplies e.2 (Witness.substC ω e.2) ||
      goalCovered db₀ proved c.negate (Witness.substC ω e.2)

/-- **The freshness check** of CakePB's `check_fresh_aspo` and `fresh_aux` for the loaded order
`L`: its auxiliary variables occur in no constraint of `db`, not in `c`, not in the objective,
and not in a literal that the witness gives a variable. -/
def LoadedOrder.fresh (L : LoadedOrder) (db : List (ℕ × PBConstr)) (obj : Option Objective)
    (c : PBConstr) (ω : Witness) : Bool :=
  db.all (L.order.avoids ·.2) && L.order.avoids c &&
    obj.all (fun f => f.lin.all fun e => !L.order.aux.contains e.1) && L.imageAvoids ω

/-- The premises of the scopes of `red C : ω` (§5.4.1): `scope leq` adds the specification
`S⪯(z↾ω, z, a)` of the loaded order, normalized, and nothing without an order; there is no
`scope geq`. -/
def redScope (ord : Option LoadedOrder) (ω : Witness) : Bool → Option (List PBConstr)
  | false => some (((ord.map (·.leSpec ω)).getD []).map normalize)
  | true => none

/-- The end of a `red` subproof with premises `db₀` and goals for the constraints `gs`: the
closing constraint is a contradiction, or every goal is covered. The order goals are also covered
when the witness leaves the variables of the order alone (§5.5.1, item 1c). A goal proved in the
scope `scope leq` counts. If a scope is used (`hs`) or the witness touches the order, the
auxiliary variables must be fresh, as in CakePB's `check_red`. -/
private def redOk (obj : Option Objective) (ord : Option LoadedOrder) (db₀ gs : List (ℕ × PBConstr))
    (ω : Witness) (c : PBConstr) (hs : Bool) (db' : List (ℕ × PBConstr))
    (proved : List Tagged) : Option ℕ → Bool
  | some q => namesContra db' q
  | none =>
    let proved := visible false proved
    ord.all (fun L => !(hs || !L.untouched ω) || L.fresh (db₀ ++ gs) obj c ω) &&
      goalCovered db₀ proved c.negate (Witness.substC ω c) &&
      ord.all (fun L => L.untouched ω || (L.leGoals ω).all (goalCovered db₀ proved c.negate)) &&
      substCovered obj db₀ gs ω c proved

/-- **The redundance check with separate goals**: as `Cslib.Logic.PL.VeriPB.redCheck`, for the
loaded order `ord`, if any, with premises `db₀` but goals `D|ω` only for the constraints `D` of
`gs`. In strengthening-to-core mode, `gs` is the core set (§5.6 of the documentation); for a
checked deletion, premises and goals are the remaining core set (§5.7.1). With an order loaded,
the order goals `O⪯(z↾ω, z, a)` must be covered too, and the scope `scope leq` adds
`S⪯(z↾ω, z, a)` to the premises (§5.4.1). -/
def redCheckOn (obj : Option Objective) (ord : Option LoadedOrder) (db₀ gs : List (ℕ × PBConstr))
    (n : ℕ) (c : PBConstr) (ω : Witness) (items : List RedItem) (qed : Option ℕ) : Option ℕ :=
  match runGoals (goalOf obj ord db₀ ω c)
      (if items.any RedItem.isScope then redScope ord ω else noScope) none ((n, c.negate) :: db₀)
      (n + 1) items [] with
  | none => none
  | some (db', n', proved) =>
    if redOk obj ord db₀ gs ω c (items.any RedItem.isScope) db' proved qed then some n' else none

/-- **The redundance check** of `red C : ω` for the objective `obj`, without an order: `¬C` takes
the number `n`, the subproof runs, and then either the closing contradiction is derived, or `C|ω`
is covered, so is `f|ω ≤ f` for an objective `f`, and so is `D|ω` for every constraint `D` of the
database, `D|ω` also when `ω` sets every literal of `D` it touches true. Returns the next number
after the subproof. -/
def redCheck (obj : Option Objective) (db₀ : List (ℕ × PBConstr)) (n : ℕ) (c : PBConstr)
    (ω : Witness) (items : List RedItem) (qed : Option ℕ) : Option ℕ :=
  redCheckOn obj none db₀ db₀ n c ω items qed

/-! ### Objective updates -/

/-- The objective `f + g`, with the weights of each variable merged and zero weights dropped, as
CakePB's `add_obj` (§5.9 of the documentation). -/
@[expose]
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

/-- The premises of the goals of `obju` from `f` to `f'`: `#1` is `f' ≥ f` and `#2` is
`f ≥ f'`. -/
def objuGoal (f f' : Objective) : GoalId → Option (List PBConstr)
  | .hash k => (hashAt [f'.geGoal f, f.geGoal f'] k).map negGoal
  | .db _ => none

/-- **The check of `obju`** from the objective `f` to `f'` (§5.9): goal `#1` is `f' ≥ f` and
goal `#2` is `f ≥ f'`, both derived from the core set `core` alone. Returns the next number after
the subproof. -/
def objuCheck (core : List (ℕ × PBConstr)) (n : ℕ) (f f' : Objective) (items : List RedItem) :
    Option ℕ :=
  match runGoals (objuGoal f f') noScope none core n items [] with
  | some (_, n', proved) =>
    if objuCovered core (visible false proved) (f'.geGoal f) &&
        objuCovered core (visible false proved) (f.geGoal f') then
      some n'
    else none
  | none => none

/-! ### Solutions -/

/-- The assignment of a list of literals: a variable is true when it is listed positively, and
false otherwise. -/
@[expose]
def assignOf (ρ : List (Literal ℕ)) (v : ℕ) : Bool := ρ.contains (v, true)

/-- **A logged solution** `ρ` solves the constraints `cs` (§5.8.1 of the documentation, without
propagation as in the kernel format, §6.1): no literal is listed with its negation, and the
coefficients of the terms of each constraint whose literals are listed reach its degree. -/
@[expose]
def solves (ρ : List (Literal ℕ)) (cs : List PBConstr) : Bool :=
  ρ.all (fun l => !ρ.contains (Std.Sat.Literal.negate l)) &&
    cs.all fun c => decide (c.degree ≤ coeffSum (c.terms.filter fun t => ρ.contains t.2))

/-- `ρ` assigns every variable of `P`, as `solx` requires in the kernel format (§6.1). -/
@[expose]
def assignsAll (ρ : List (Literal ℕ)) (P : List ℕ) : Bool :=
  P.all fun x => ρ.contains (x, true) || ρ.contains (x, false)

/-- `ρ` assigns every variable of the objective, as `soli` requires (§5.8.2). -/
@[expose]
def assigns (ρ : List (Literal ℕ)) (f : Objective) : Bool := assignsAll ρ (f.lin.map (·.1))

/-- Lower the bound `d`, if any, to `v`. -/
private def lowerTo (d : Option ℤ) (v : ℤ) : Option ℤ := some (d.elim v (min · v))

/-! ### Preserved sets -/

/-- The values of the preserved variables `P` under `σ`: the projection of `σ` to `P`. -/
@[expose]
def proj (P : List ℕ) (σ : ℕ → Bool) : List Bool := P.map σ

/-- **The solution-excluding constraint** of `ρ` over `P` (§5.8.3): `∑ x` over the variables of
`P` false in `ρ`, plus `∑ ¬x` over those true, at least `1`. It holds exactly at the assignments
whose projection to `P` differs from that of `ρ`. A variable listed twice in `P` gives one term, so
the constraint is normalized: `preserved:` is a set (VeriPB and CakePB). -/
@[expose]
def exclusion (P : List ℕ) (ρ : List (Literal ℕ)) : PBConstr :=
  ⟨P.dedup.map fun x => (1, (x, !assignOf ρ x)), 1⟩

/-- The witness `ω` leaves the preserved variables, if any, alone (CakePB's `check_pres`). -/
@[expose]
def presFree (pres : Option (List ℕ)) (ω : Witness) : Bool :=
  pres.all fun P => ω.all fun e => !P.contains e.1

/-- The lists `P` and `Q` name the same set of variables: each contains the other, whatever the
order and the duplicates (`epreserved`, §5.11.4, and the preserved sets of `EQUIENUMERABLE`). -/
@[expose]
def sameVars (P Q : List ℕ) : Bool := P.all Q.contains && Q.all P.contains

theorem sameVars_iff {P Q : List ℕ} : sameVars P Q = true ↔ ∀ x, x ∈ P ↔ x ∈ Q := by
  simp only [sameVars, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

/-- The redundance check, with a witness that leaves the preserved variables alone. -/
private def redCheckP (pres : Option (List ℕ)) (obj : Option Objective) (ord : Option LoadedOrder)
    (db₀ gs : List (ℕ × PBConstr)) (n : ℕ) (c : PBConstr) (ω : Witness) (items : List RedItem)
    (qed : Option ℕ) : Option ℕ :=
  if presFree pres ω then redCheckOn obj ord db₀ gs n c ω items qed else none

/-! ### Defining orders -/

/-- The end of a proof of the goals `gs`: the closing constraint is a contradiction, or every
goal is trivially true or proved by a `proofgoal` block. -/
private def hashGoalsOk (gs : List PBConstr) (db' : List (ℕ × PBConstr))
    (proved : List (List PBConstr)) : Option ℕ → Bool
  | some q => namesContra db' q
  | none => gs.all fun G => G.normalize.degree == 0 || proved.contains (negGoal G)

/-- **The check of the goals `#1` … `#N`**, the constraints `gs`, from the premises `db` whose next
number is `n` (`Cslib.Logic.PL.VeriPB.hashGoalsOk`). Returns the next number after the proof. -/
private def hashGoalsCheck (db : List (ℕ × PBConstr)) (n : ℕ) (gs : List PBConstr)
    (p : OrderProof) : Option ℕ :=
  match runGoals (fun | .hash k => (hashAt gs k).map negGoal | .db _ => none) noScope none db n
      p.items [] with
  | none => none
  | some (db', n', proved) =>
    if hashGoalsOk gs db' (visible false proved) p.qed then some n' else none

namespace Order

/-- **The check of a specification** (§5.3; CakePB's `check_spec`): each constraint `C` follows
by `red C : ω` from the constraints before it, numbered from `n`, with a witness that sets only
auxiliary variables (CakePB's `check_support`). -/
private def specCheckFrom (O : Order) :
    List (ℕ × PBConstr) → ℕ → List PBConstr → List SpecStep → Bool
  | _, _, [], [] => true
  | db, n, c :: cs, p :: ps =>
    p.witness.all (fun e => O.aux.contains e.1) &&
      match redCheck none db n c p.witness (p.sub.getD []) p.qed with
      | some n' =>
        let m := if p.sub.isSome then n' else n
        specCheckFrom O ((m, c.normalize) :: db) (m + 1) cs ps
      | none => false
  | _, _, _, _ => false

/-- **The transitivity check** (§5.3) with the fresh variables `w`, `b` and `c`, as CakePB's
`check_transitivity`: `w` is as long as `u`, `b` and `c` as `a`, and `u`, `v`, `a`, `w`, `b`, `c`
are distinct variables. The premises `S⪯(u, v, a)`, `S⪯(v, w, b)`, `S⪯(u, w, c)`, `O⪯(u, v, a)`
and `O⪯(v, w, b)` are numbered from `1`, and the goals are the constraints of `O⪯(u, w, c)`.
Returns the next number, from which the reflexivity proof is numbered, as in VeriPB and
CakePB. -/
private def transCheck (O : Order) (w : TransVars) (p : OrderProof) : Option ℕ :=
  if w.right.length == O.left.length && w.aux₁.length == O.aux.length &&
      w.aux₂.length == O.aux.length && decide (O.vars ++ w.right ++ w.aux₁ ++ w.aux₂).Nodup then
    let u := posVals O.left
    let v := posVals O.right
    let a := posVals O.aux
    let x := posVals w.right
    let prem := O.specC u v a ++ O.specC v x (posVals w.aux₁) ++ O.specC u x (posVals w.aux₂) ++
      O.instC u v a ++ O.instC v x (posVals w.aux₁)
    hashGoalsCheck (initDb prem) (prem.length + 1) (O.instC u x (posVals w.aux₂)) p
  else none

/-- **The reflexivity check** (§5.3), numbered from `n`: the premises `S⪯(u, u, a)`, normalized,
take the numbers from `n`, and the goals are the constraints of `O⪯(u, u, a)`. -/
private def reflCheck (O : Order) (n : ℕ) (p : OrderProof) : Bool :=
  let prem := (O.specC (posVals O.left) (posVals O.left) (posVals O.aux)).map normalize
  (hashGoalsCheck (pushAll [] n prem).1 (pushAll [] n prem).2
    (O.instC (posVals O.left) (posVals O.left) (posVals O.aux)) p).isSome

/-- **The check of `def_order`** (§5.3; CakePB's `check_spec`, `check_good_aord`,
`check_transitivity` and `check_reflexivity`): the order is well formed, the derivation `spec`
of its specification, numbered from `1`, is accepted, and so are its transitivity proof, with the
fresh variables `w`, and its reflexivity proof. -/
def defCheck (O : Order) (spec : List SpecStep) (w : TransVars) (trans refl : OrderProof) :
    Bool :=
  O.wellFormed && specCheckFrom O [] 1 O.spec spec &&
    match O.transCheck w trans with
    | some n => O.reflCheck n refl
    | none => false

end Order

/-! ### Dominance -/

/-- The premises of the `#` goals of `dom C : ω` (§5.4.2) for the loaded order `L`: the negations
of the order goals `O⪯(z↾ω, z, a)`, then the constraints `O⪯(z, z↾ω, a)` to refute, normalized,
then the negation of the objective goal `f|ω ≤ f`, if there is an objective. -/
def domHashPremises (obj : Option Objective) (L : LoadedOrder) (ω : Witness) :
    List (List PBConstr) :=
  (L.leGoals ω).map negGoal ++ [(L.geGoals ω).map normalize] ++
    (obj.map fun f => negGoal (objGoal f ω)).toList

/-- The premises of the scopes of `dom C : ω` (§5.4.2): `scope leq` adds `S⪯(z↾ω, z, a)` and
`scope geq` adds `S⪯(z, z↾ω, a)`, normalized. -/
def domScope (L : LoadedOrder) (ω : Witness) : Bool → Option (List PBConstr)
  | false => some ((L.leSpec ω).map normalize)
  | true => some ((L.geSpec ω).map normalize)

/-- The end of a `dom` subproof (`Cslib.Logic.PL.VeriPB.domCheck`). Goal `#N + 1` counts when
proved outside the scopes or in `scope geq`; the others when proved outside the scopes or in
`scope leq`. -/
private def domOk (obj : Option Objective) (L : LoadedOrder) (db core : List (ℕ × PBConstr))
    (ω : Witness) (c : PBConstr) (db' : List (ℕ × PBConstr)) (proved : List Tagged) :
    Option ℕ → Bool
  | some q => namesContra db' q
  | none =>
    (visible true proved).contains ((L.geGoals ω).map normalize) &&
      (L.leGoals ω).all (goalCovered db (visible false proved) c.negate) &&
      substCovered obj db core ω c (visible false proved)

/-- **The dominance check** of `dom C : ω` (§5.4.2) for the loaded order `L`, the database `db`
and its core set `core`, as CakePB's `Dom` step of `check_cstep`. The witness must leave the
preserved variables alone, and the auxiliary variables of `L` must be fresh
(`Cslib.Logic.PL.VeriPB.LoadedOrder.fresh`). `¬C` takes the number `n`, and the subproof runs
from the database and `¬C`, the scope `scope leq` adding `S⪯(z↾ω, z, a)` and `scope geq` adding
`S⪯(z, z↾ω, a)`; then either the closing constraint is a contradiction, or
* goal `#N + 1`, the constraints `O⪯(z, z↾ω, a)`, was refuted by a `proofgoal` block outside the
  scopes or in `scope geq`,
* the order goals `O⪯(z↾ω, z, a)` and the objective goal `f|ω ≤ f`, for an objective `f`, are
  covered,
* and `D|ω` is covered for every constraint `D` of the core set (not of the derived set), its
  label being its number,

the last two outside the scopes or in `scope leq`. Returns the next number after the subproof. -/
def domCheck (pres : Option (List ℕ)) (obj : Option Objective) (L : LoadedOrder)
    (db core : List (ℕ × PBConstr)) (n : ℕ) (c : PBConstr) (ω : Witness) (items : List RedItem)
    (qed : Option ℕ) : Option ℕ :=
  if presFree pres ω && L.fresh (db ++ core) obj c ω then
    match runGoals (fun
        | .hash k => hashAt (domHashPremises obj L ω) k
        | .db i => (lookup core i).map fun D => negGoal (Witness.substC ω D))
      (domScope L ω) none ((n, c.negate) :: db) (n + 1) items [] with
    | none => none
    | some (db', n', proved) => if domOk obj L db core ω c db' proved qed then some n' else none
  else none

/-! ### Changing the preserved set -/

/-- The constraint `ℓ ∨ C`: the literal `ℓ` with the degree of `C` as coefficient, added to `C`. -/
private def orLit (l : Literal ℕ) (c : PBConstr) : PBConstr := ⟨(c.degree, l) :: c.terms, c.degree⟩

/-- **The goals of `preserved_add x : C` and `preserved_rm x : C`** (§5.10): `#1` is `x ⇒ C`, that
is `¬x ∨ C`, and `#2` is `x ⇐ C`, that is `x ∨ ¬C`, as CakePB's `change_pres_subgoals`; together
they say `x ⇔ C`. -/
def presGoals (x : ℕ) (c : PBConstr) : List PBConstr :=
  [orLit (x, false) c.normalize, orLit (x, true) c.negate]

/-- **The check of `preserved_add x : C` and `preserved_rm x : C`** with the preserved set `P`, as
CakePB's `check_change_pres`: the variables of `C` are in `P` and are not `x` (`pres_only`), and
the goals `x ⇒ C` and `x ⇐ C` follow from the core set `core`: each is trivially true or proved
by a `proofgoal` block, whose negated goal takes the next number from `n`. Returns the next number
after the subproof. -/
def presChangeCheck (core : List (ℕ × PBConstr)) (n : ℕ) (P : List ℕ) (x : ℕ) (c : PBConstr)
    (items : List RedItem) : Option ℕ :=
  if c.normalize.terms.all fun t => P.contains (termVar t) && termVar t != x then
    hashGoalsCheck core n (presGoals x c) ⟨items, none⟩
  else none

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
  /-- The current preserved set, if any: that of the input (`preserved:`), as changed by
  `preserved_add` and `preserved_rm` (§5.10). -/
  pres : Option (List ℕ)
  /-- The projections to the preserved set of the solutions logged by `solx`, latest first. -/
  logged : List (List Bool)
  /-- The orders defined by `def_order`, by name, latest first (§5.3). -/
  orders : List (String × Order)
  /-- The loaded order, if any (§5.3). -/
  order : Option LoadedOrder
  /-- The name of the loaded order, if any, for `eord_loaded` (§5.11.3). -/
  orderName : Option String
  /-- The preserved set has been changed (§5.10); `solx` is then rejected (§5.8.3). -/
  presChanged : Bool
  deriving DecidableEq, Repr

/-- The initial state for the formula `F`, the objective `obj` and the preserved set `pres`: the
constraints, numbered from `1`, form the database and the core set. -/
@[expose]
def State.init (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) : State :=
  ⟨initDb F, F.length + 1, none, none, initDb F, true, false, obj, pres, [], [], none, none,
    false⟩

/-- Log the solution `ρ` of the database in the state `s` for the formula `F` and the input
objective `obj`. Its value under the current objective lowers `dbound`. It lowers `bound` too
if no unchecked deletion has happened, at that value, or else if it solves `F`, at its value
under the input objective. Any other solution leaves `bound` unchanged. -/
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

/-- Add the constraint `c`, derived by `red` or `dom`, to the state `s` under the number `m`: it is
a derived constraint, or a core constraint in strengthening-to-core mode (§5.6). -/
@[expose]
def State.addStrengthened (s : State) (m : ℕ) (c : PBConstr) : State :=
  { s with
    db := (m, c.normalize) :: s.db, next := m + 1,
    core := if s.tcb then (m, c.normalize) :: s.core else s.core }

/-- The constraint numbers that a step deletes. -/
private def Step.delIds : Step → List ℕ
  | .del ids => ids
  | _ => []

/-- The orders `O` and `O'` have the same variables, in order, and the same constraints in their
specifications and definitions, in order, up to normalization and the order of terms
(`eord_def`, §5.11.3). -/
private def sameOrder (O O' : Order) : Bool :=
  O.left == O'.left && O.right == O'.right && O.aux == O'.aux &&
    O.spec.isEqv O'.spec (fun c d => sameUpToOrder c.normalize d.normalize) &&
    O.defn.isEqv O'.defn (fun c d => sameUpToOrder c.normalize d.normalize)

/-- **One top-level step** for the input formula `F` and the objective `obj`.

* An implicational step adds a derived constraint. The untyped deletion `del id` of a core
  constraint counts as unchecked, and it is rejected in strengthening-to-core mode or while an
  order is loaded.
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
  already in the core set changes nothing (§5.1). `strengthening_to_core on` moves all of them.
* `def_order` stores an order whose specification, definition, transitivity and reflexivity
  check; `load_order` loads a stored order over as many literals as it has left variables, none
  on an auxiliary variable, and moves every constraint to the core set; `load_order;` unloads it.
  `eord_def` and `eord_loaded` check the stored and the loaded order and change nothing.
* `dom` needs a loaded order, and adds a derived constraint, or a core constraint in
  strengthening-to-core mode.
* While an order is loaded (§5.7.4), as in strengthening-to-core mode, an unchecked deletion of
  core constraints needs an empty derived set. `red` and checked deletion get the order goals; as
  in VeriPB and CakePB, a checked deletion may still take a witness, which §5.7.4 forbids. -/
def stepTop (F : List PBConstr) (obj : Option Objective) (s : State) : TopStep → Option State
  | .step st =>
    match runStep s.db s.next st with
    | some (db', n') =>
      if (s.tcb || s.order.isSome) && s.core.any (fun e => st.delIds.contains e.1) then none
      else some { s with
        db := db', next := n',
        core := s.core.filter (fun e => !st.delIds.contains e.1),
        chk := s.chk && !s.core.any (fun e => st.delIds.contains e.1) }
    | none => none
  | .red c ω sub q =>
    match redCheckP s.pres s.obj s.order s.db (if s.tcb then s.core else s.db) s.next c ω
      (sub.getD []) q with
    | some n' => some (s.addStrengthened (if sub.isSome then n' else s.next) c)
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
        (!s.tcb && s.order.isNone || s.db.all (s.core.contains ·)) then
      some { s with
        db := s.db.filter (fun e => !ids.contains e.1),
        core := s.core.filter (fun e => !ids.contains e.1), chk := false }
    else none
  | .delcChecked i ω sub q =>
    match lookup s.core i with
    | some c =>
      if !s.tcb || ω.isEmpty && q.isSome then
        match redCheckP s.pres s.obj s.order (s.core.filter (·.1 != i))
            (s.core.filter (·.1 != i)) s.next c ω (sub.getD []) q with
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
      if s.chk && !s.presChanged && solves ρ (s.db.map (·.2)) && assignsAll ρ P then
        some { (s.log F obj ρ).addCore (exclusion P ρ) with
          logged := proj P (assignOf ρ) :: s.logged }
      else none
    | _, _ => none
  | .defOrder name O sp w tp rp =>
    if O.defCheck sp w tp rp then some { s with orders := (name, O) :: s.orders } else none
  | .loadOrder name z =>
    match s.orders.lookup name with
    | some O =>
      if z.length == O.left.length && z.all (fun l => !O.aux.contains l.1) then
        some { s with core := s.db, order := some ⟨O, z⟩, orderName := some name }
      else none
    | none => none
  | .unloadOrder => some { s with order := none, orderName := none }
  | .eordDef name O =>
    if (s.orders.lookup name).any (sameOrder O) then some s else none
  | .eordLoaded name z =>
    if s.orderName == some name && s.order.any (·.lits == z) then some s else none
  | .presChange add x c sub =>
    match s.pres with
    | some P =>
      match presChangeCheck s.core s.next P x c (sub.getD []) with
      | some n' =>
        some { s with
          pres := some (if add then P.insert x else P.filter (· != x)), presChanged := true,
          next := n' }
      | none => none
    | none => none
  | .epreserved vs =>
    if s.pres.any (sameVars vs) then some s else none
  | .econstr c j =>
    if (lookup s.db j).any (fun d => sameUpToOrder d.normalize c.normalize) then some s else none
  | .dom c ω sub q =>
    match s.order with
    | some L =>
      match domCheck s.pres s.obj L s.db s.core s.next c ω (sub.getD []) q with
      | some n' => some (s.addStrengthened (if sub.isSome then n' else s.next) c)
      | none => none
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
@[expose]
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
@[expose]
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
@[expose]
def checkRed (F : List PBConstr) (obj : Option Objective) (P : RedProof)
    (pres : Option (List ℕ) := none) : Bool :=
  match runTop F obj (State.init F obj pres) P.steps with
  | some s => checkConclusion F obj s P.conclusion
  | none => false

/-! ### Equations of the checker -/

/-! The bodies of `Cslib.Logic.PL.VeriPB.stepTop` and `Cslib.Logic.PL.VeriPB.runTop` are not
exposed; these equations are what a checker computing the same steps needs. -/

theorem runTop_nil (F : List PBConstr) (obj : Option Objective) (s : State) :
    runTop F obj s [] = some s := by
  simp only [runTop]

theorem runTop_cons (F : List PBConstr) (obj : Option Objective) (s : State) (t : TopStep)
    (ts : List TopStep) :
    runTop F obj s (t :: ts) = (stepTop F obj s t).bind fun s' => runTop F obj s' ts := by
  simp only [runTop]
  cases stepTop F obj s t <;> rfl

/-- An implicational step that deletes nothing changes only the database and the next number. -/
theorem stepTop_step_of_ne_del (F : List PBConstr) (obj : Option Objective) (s : State)
    {st : Step} (h : ∀ ids, st ≠ .del ids) :
    stepTop F obj s (.step st) =
      (runStep s.db s.next st).map fun r => { s with db := r.1, next := r.2 } := by
  have hd : st.delIds = [] := by cases st <;> simp_all [Step.delIds]
  simp only [stepTop, hd]
  cases runStep s.db s.next st <;> simp

/-- The untyped deletion `del id ids` (§5.7.2). -/
theorem stepTop_step_del (F : List PBConstr) (obj : Option Objective) (s : State) (ids : List ℕ) :
    stepTop F obj s (.step (.del ids)) =
      match runStep s.db s.next (.del ids) with
      | some (db', n') =>
        if (s.tcb || s.order.isSome) && s.core.any (fun e => ids.contains e.1) then none
        else some { s with
          db := db', next := n',
          core := s.core.filter (fun e => !ids.contains e.1),
          chk := s.chk && !s.core.any (fun e => ids.contains e.1) }
      | none => none := by
  simp only [stepTop, Step.delIds]
  rfl

/-- The deletion `deld ids` of derived constraints (§5.7.1). -/
theorem stepTop_deld (F : List PBConstr) (obj : Option Objective) (s : State) (ids : List ℕ) :
    stepTop F obj s (.deld ids) =
      if decide ids.Nodup && ids.all (fun i => (lookup s.db i).isSome) &&
          !s.core.any (fun e => ids.contains e.1) then
        some { s with db := s.db.filter fun e => !ids.contains e.1 }
      else none := by
  simp only [stepTop]

/-- The unchecked deletion `delc ids` of core constraints (§5.7.1). -/
theorem stepTop_delc (F : List PBConstr) (obj : Option Objective) (s : State) (ids : List ℕ) :
    stepTop F obj s (.delc ids) =
      if decide ids.Nodup && ids.all (fun i => s.core.any (·.1 == i)) &&
          (!s.tcb && s.order.isNone || s.db.all (s.core.contains ·)) then
        some { s with
          db := s.db.filter (fun e => !ids.contains e.1),
          core := s.core.filter (fun e => !ids.contains e.1), chk := false }
      else none := by
  simp only [stepTop]

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

/-- The premise lists that `σ` refutes: those with a constraint false at `σ`. -/
private def Refuted (σ : ℕ → Bool) (proved : List (List PBConstr)) : Prop :=
  ∀ ps ∈ proved, ¬ ∀ p ∈ ps, p.Holds σ

/-- A refuted negation gives the goal. -/
private theorem Refuted.holds {σ : ℕ → Bool} {proved : List (List PBConstr)} (hp : Refuted σ proved)
    {G : PBConstr} (h : proved.contains (negGoal G) = true) : G.Holds σ := by
  have := hp _ (List.contains_iff_mem.1 h)
  simpa [negGoal, holds_negate] using this

/-- A constraint of degree `0` after normalization is trivially true. -/
theorem holds_of_normalize_degree_eq_zero {σ : ℕ → Bool} {c : PBConstr}
    (h : c.normalize.degree = 0) : c.Holds σ := by
  rw [← holds_normalize]; unfold Holds; rw [h]; exact Nat.zero_le _

private theorem objuCovered_holds {σ : ℕ → Bool} {core : List (ℕ × PBConstr)}
    {proved : List (List PBConstr)} {G : PBConstr} (hdb : AllHold σ core)
    (hp : Refuted σ proved) (h : objuCovered core proved G = true) : G.Holds σ := by
  unfold objuCovered at h
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with (h | ⟨e, he, heq⟩) | h
  · exact holds_of_normalize_degree_eq_zero h
  · rw [← holds_normalize]; exact Holds.of_sameUpToOrder (hdb e he) heq
  · exact hp.holds h

private theorem goalCovered_holds {σ : ℕ → Bool} {db₀ : List (ℕ × PBConstr)}
    {proved : List (List PBConstr)} {negC G : PBConstr} (hdb : AllHold σ db₀)
    (hp : Refuted σ proved) (hneg : negC.Holds σ) (h : goalCovered db₀ proved negC G = true) :
    G.Holds σ := by
  unfold goalCovered at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact objuCovered_holds hdb hp h
  · exact Holds.of_weakImplies hneg h

private theorem allHold_pushAll {σ : ℕ → Bool} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (ps : List PBConstr), AllHold σ db →
      (∀ p ∈ ps, p.Holds σ) → AllHold σ (pushAll db n ps).1
  | _, _, [], hdb, _ => hdb
  | db, n, p :: ps, hdb, hps =>
    allHold_pushAll ((n, p) :: db) (n + 1) ps
      (List.forall_mem_cons.2 ⟨hps p List.mem_cons_self, hdb⟩)
      fun q hq => hps q (List.mem_cons_of_mem _ hq)

/-- The premises of the scope `sc` hold at `σ`: always outside the scopes, and in the scope `b`
when `scope b` gives premises that hold. -/
private def ScopeHolds (scope : Bool → Option (List PBConstr)) (σ : ℕ → Bool) :
    Option Bool → Prop
  | none => True
  | some b => ∀ S, scope b = some S → ∀ p ∈ S, p.Holds σ

/-- The tagged premise lists that `σ` refutes wherever the premises of their scope hold. -/
private def RefutedIn (scope : Bool → Option (List PBConstr)) (σ : ℕ → Bool)
    (proved : List Tagged) : Prop :=
  ∀ e ∈ proved, ScopeHolds scope σ e.1 → ¬ ∀ p ∈ e.2, p.Holds σ

mutual

private theorem runItem_sound {σ : ℕ → Bool} {goal : GoalId → Option (List PBConstr)} :
    ∀ (scope : Bool → Option (List PBConstr)) (cur : Option Bool) (db : List (ℕ × PBConstr))
      (n : ℕ) (it : RedItem) (proved : List Tagged) (db' : List (ℕ × PBConstr))
      (n' : ℕ) (proved' : List Tagged),
      (ScopeHolds scope σ cur → AllHold σ db) → RefutedIn scope σ proved →
      runItem goal scope cur db n it proved = some (db', n', proved') →
      (ScopeHolds scope σ cur → AllHold σ db') ∧ RefutedIn scope σ proved'
  | _, cur, db, n, .step s, proved, db', n', proved', hdb, hp, h => by
    simp only [runItem, Option.map_eq_some_iff] at h
    obtain ⟨⟨db₁, n₁⟩, h₁, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨fun hsc => runStep_sound _ _ _ _ _ (hdb hsc) h₁, hp⟩
  | _, cur, db, n, .goal g sub q, proved, db', n', proved', hdb, hp, h => by
    simp only [runItem] at h
    split at h
    · cases h
    · rename_i ps hps
      split at h
      · rename_i db₂ n₂ h₂
        split at h
        · rename_i hq
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -, rfl⟩ := h
          refine ⟨hdb, List.forall_mem_cons.2 ⟨fun hsc hall => ?_, hp⟩⟩
          have h₁ := allHold_pushAll db n ps (hdb hsc) hall
          simp [(runSteps_sound _ _ sub _ _ h₁ h₂).not_namesContra] at hq
        · cases h
      · cases h
  | scope, cur, db, n, .scope b inner, proved, db', n', proved', hdb, hp, h => by
    simp only [runItem] at h
    split at h
    · rename_i hcur
      cases cur with
      | some _ => simp at hcur
      | none =>
      split at h
      · cases h
      · rename_i S hS
        split at h
        · rename_i db₂ n₂ proved₂ h₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -, rfl⟩ := h
          exact ⟨hdb, (runGoals_sound _ (some b) _ _ inner proved db₂ n₂ proved₂
            (fun hsc => allHold_pushAll db n S (hdb trivial) (hsc S hS)) hp h₂).2⟩
        · cases h
    · cases h

private theorem runGoals_sound {σ : ℕ → Bool} {goal : GoalId → Option (List PBConstr)} :
    ∀ (scope : Bool → Option (List PBConstr)) (cur : Option Bool) (db : List (ℕ × PBConstr))
      (n : ℕ) (items : List RedItem) (proved : List Tagged) (db' : List (ℕ × PBConstr))
      (n' : ℕ) (proved' : List Tagged),
      (ScopeHolds scope σ cur → AllHold σ db) → RefutedIn scope σ proved →
      runGoals goal scope cur db n items proved = some (db', n', proved') →
      (ScopeHolds scope σ cur → AllHold σ db') ∧ RefutedIn scope σ proved'
  | _, _, db, n, [], proved, db', n', proved', hdb, hp, h => by
    simp only [runGoals, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨hdb, hp⟩
  | scope, cur, db, n, it :: items, proved, db', n', proved', hdb, hp, h => by
    simp only [runGoals] at h
    split at h
    · rename_i db₁ n₁ proved₁ h₁
      have := runItem_sound scope cur db n it proved db₁ n₁ proved₁ hdb hp h₁
      exact runGoals_sound scope cur db₁ n₁ items proved₁ db' n' proved' this.1 this.2 h
    · cases h

end

/-- **A top-level run is sound**: an assignment of the premises refutes, wherever the premises of
their scope hold, the lists the subproof refuted, and satisfies its final database. -/
private theorem runGoals_top {σ : ℕ → Bool} {goal : GoalId → Option (List PBConstr)}
    {scope : Bool → Option (List PBConstr)} {db db' : List (ℕ × PBConstr)} {n n' : ℕ}
    {items : List RedItem} {proved : List Tagged} (hdb : AllHold σ db)
    (h : runGoals goal scope none db n items [] = some (db', n', proved)) :
    AllHold σ db' ∧ RefutedIn scope σ proved := by
  obtain ⟨h₁, h₂⟩ := runGoals_sound scope none db n items [] db' n' proved (fun _ => hdb)
    (by simp [RefutedIn]) h
  exact ⟨h₁ trivial, h₂⟩

/-- Where the premises of the scope `b` hold, the lists visible in it are refuted. -/
private theorem RefutedIn.visible {scope : Bool → Option (List PBConstr)} {σ : ℕ → Bool}
    {proved : List Tagged} (hp : RefutedIn scope σ proved) {b : Bool}
    (hb : ScopeHolds scope σ (some b)) : Refuted σ (visible b proved) := by
  intro ps hps
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hps
  obtain ⟨he, hb'⟩ := List.mem_filter.1 he
  refine hp e he ?_
  rcases e with ⟨_ | b', ps⟩
  · trivial
  · simp only [Option.all_some, beq_iff_eq] at hb'
    subst hb'
    exact hb

/-- Without scopes, every list is refuted. -/
private theorem scopeHolds_noScope (σ : ℕ → Bool) (b : Bool) :
    ScopeHolds noScope σ (some b) := fun S h => by simp [noScope] at h

/-- The goals shared by `red` and `dom` hold at `σ ∘ ω`. -/
private theorem substCovered_sound {σ : ℕ → Bool} {obj : Option Objective}
    {db₀ gs : List (ℕ × PBConstr)} {ω : Witness} {c : PBConstr} {proved : List (List PBConstr)}
    (hdb : AllHold σ db₀) (hgs : AllHold σ gs) (hp : Refuted σ proved)
    (hnegC : c.negate.Holds σ) (h : substCovered obj db₀ gs ω c proved = true) :
    AllHold (Witness.apply σ ω) gs ∧ objValue obj (Witness.apply σ ω) ≤ objValue obj σ := by
  simp only [substCovered, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨hobj, hdbg⟩ := h
  refine ⟨fun e he => ?_, ?_⟩
  · rcases hdbg e he with (ht | hw) | hg
    · exact Witness.Holds.apply_of_touchedTrue ht (hgs e he)
    · rw [← Witness.holds_substC]; exact Holds.of_weakImplies (hgs e he) hw
    · rw [← Witness.holds_substC]; exact goalCovered_holds hdb hp hnegC hg
  · cases obj with
    | none => exact le_rfl
    | some f =>
      simp only [Option.all_some] at hobj
      exact (holds_objGoal σ f ω).1 (goalCovered_holds hdb hp hnegC hobj)

/-- The objective's value depends only on the values of its variables. -/
private theorem objValue_congr {obj : Option Objective} {σ σ' : ℕ → Bool}
    (h : ∀ f ∈ obj, ∀ e ∈ f.lin, σ' e.1 = σ e.1) : objValue obj σ' = objValue obj σ := by
  cases obj with
  | none => rfl
  | some f =>
    simp only [objValue, Objective.eval, linVal]
    congr 2
    exact List.map_congr_left fun e he => by rw [h f rfl e he]

/-- The facts that freshness gives about an assignment `σ'` agreeing with `σ` off the auxiliary
variables. -/
private theorem LoadedOrder.fresh_agree {L : LoadedOrder} {db : List (ℕ × PBConstr)}
    {obj : Option Objective} {c : PBConstr} {ω : Witness} (h : L.fresh db obj c ω = true)
    {σ σ' : ℕ → Bool} (hag : ∀ v ∉ L.order.aux, σ' v = σ v) :
    (∀ e ∈ db, (e.2.Holds σ' ↔ e.2.Holds σ)) ∧ (c.Holds σ' ↔ c.Holds σ) ∧
      objValue obj σ' = objValue obj σ ∧ L.imageAvoids ω = true := by
  simp only [fresh, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hdb, hc⟩, hobj⟩, hω⟩ := h
  refine ⟨fun e he => Order.holds_iff_of_avoids (hdb e he) hag,
    Order.holds_iff_of_avoids hc hag, objValue_congr fun f hf e he => hag _ ?_, hω⟩
  rw [Option.mem_def] at hf
  subst hf
  simp only [Option.all_some, List.all_eq_true] at hobj
  simpa using hobj e he

/-- **The goals of a `red` subproof hold**: an assignment `σ` of the premises, of the goal
constraints, of `¬C` and, if a scope is used, of `S⪯(z↾ω, z, a)` is mapped by the witness to one
of `C` and the goal constraints, with no larger objective value; and the order goals hold at `σ`
unless the witness leaves the order alone. -/
private theorem redOk_sound {σ : ℕ → Bool} {obj : Option Objective} {ord : Option LoadedOrder}
    {db₀ gs : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr} {ω : Witness}
    {items : List RedItem} {db' : List (ℕ × PBConstr)} {proved : List Tagged}
    (hdb : AllHold σ db₀) (hgs : AllHold σ gs) (hnegC : c.negate.Holds σ)
    (hS : items.any RedItem.isScope = true →
      ∀ p ∈ ((ord.map (·.leSpec ω)).getD []).map normalize, p.Holds σ)
    (hrun : runGoals (goalOf obj ord db₀ ω c)
      (if items.any RedItem.isScope then redScope ord ω else noScope) none
      ((n, c.negate) :: db₀) (n + 1) items [] = some (db', n', proved))
    (hok : redOk obj ord db₀ gs ω c (items.any RedItem.isScope) db' proved none = true) :
    c.Holds (Witness.apply σ ω) ∧ AllHold (Witness.apply σ ω) gs ∧
      objValue obj (Witness.apply σ ω) ≤ objValue obj σ ∧
      ∀ L ∈ ord, L.untouched ω = true ∨ ∀ G ∈ L.leGoals ω, G.Holds σ := by
  have hneg : AllHold σ ((n, c.negate) :: db₀) := List.forall_mem_cons.2 ⟨hnegC, hdb⟩
  obtain ⟨-, hp⟩ := runGoals_top hneg hrun
  have hp' : Refuted σ (visible false proved) := by
    refine hp.visible ?_
    split
    · rename_i hs
      intro S hS'
      simp only [redScope, Option.some.injEq] at hS'
      exact hS'.symm ▸ hS hs
    · exact scopeHolds_noScope σ false
  simp only [redOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨-, hself⟩, hord⟩, hsub⟩ := hok
  obtain ⟨hgs', hobj⟩ := substCovered_sound hdb hgs hp' hnegC hsub
  refine ⟨?_, hgs', hobj, fun L hL => ?_⟩
  · rw [← Witness.holds_substC]
    exact goalCovered_holds hdb hp' hnegC hself
  · rw [Option.mem_def] at hL
    subst hL
    simp only [Option.all_some, Bool.or_eq_true, List.all_eq_true] at hord
    exact hord.imp id fun hg G hG => goalCovered_holds hdb hp' hnegC (hg G hG)

/-- **The redundance check is sound**, with separate goals: an assignment `σ` satisfying the
premises `db₀` and the goal constraints `gs` either satisfies `C` too, or `σ ∘ ω` satisfies `gs`
and `C`. Either way, the objective does not increase, and the result is below `σ` in the loaded
order, if it is good. Goals proved in the scope `scope leq` hold because the auxiliary variables
are fresh: `σ` can be given values of them satisfying `S⪯(z↾ω, z, a)` (CakePB's
`substitution_redundancy_obj_po_spec`). -/
theorem redCheckOn_sound {σ : ℕ → Bool} {obj : Option Objective} {ord : Option LoadedOrder}
    {db₀ gs : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr} {ω : Witness}
    {items : List RedItem} {qed : Option ℕ} (hL : ∀ L ∈ ord, L.Good) (hdb : AllHold σ db₀)
    (hgs : AllHold σ gs) (h : redCheckOn obj ord db₀ gs n c ω items qed = some n') :
    ∃ τ, (τ = σ ∨ τ = Witness.apply σ ω) ∧ AllHold τ ((n', c.normalize) :: gs) ∧
      objValue obj τ ≤ objValue obj σ ∧ ∀ L ∈ ord, L.Le τ σ := by
  by_cases hc : c.Holds σ
  · exact ⟨σ, .inl rfl, List.forall_mem_cons.2 ⟨(holds_normalize σ c).2 hc, hgs⟩, le_rfl,
      fun L hL' => (hL L hL').le_refl σ⟩
  unfold redCheckOn at h
  split at h
  · cases h
  rename_i db' n'' proved hrun
  split at h
  swap
  · cases h
  rename_i hok
  cases h
  have hnegC : c.negate.Holds σ := (holds_negate σ c).2 hc
  refine ⟨Witness.apply σ ω, .inr rfl, ?_⟩
  cases qed with
  | some q =>
    have hneg : AllHold σ ((n, c.negate) :: db₀) := List.forall_mem_cons.2 ⟨hnegC, hdb⟩
    obtain ⟨hall, -⟩ := runGoals_top hneg hrun
    simp [redOk, hall.not_namesContra] at hok
  | none =>
  cases hord : ord with
  | none =>
    subst hord
    obtain ⟨hc', hgs', hobj, -⟩ := redOk_sound hdb hgs hnegC (by simp) hrun hok
    exact ⟨List.forall_mem_cons.2 ⟨(holds_normalize _ c).2 hc', hgs'⟩, hobj, by simp⟩
  | some L =>
  subst hord
  have hLg := hL L rfl
  by_cases hneed : (items.any RedItem.isScope || !L.untouched ω) = true
  · -- The auxiliary variables are fresh: run the subproof at `σ` with values of them
    -- satisfying the specification.
    have hfresh : L.fresh (db₀ ++ gs) obj c ω = true := by
      simp only [redOk, Bool.and_eq_true, Option.all_some, Bool.or_eq_true, Bool.not_eq_true',
        hneed] at hok
      simpa using hok.1.1.1
    obtain ⟨hdbag, hcag, hobjag, hω⟩ := LoadedOrder.fresh_agree hfresh
      (fun v hv => assignOn_of_not_mem hv [] σ)
    clear hdbag hcag hobjag
    obtain ⟨ρ, -, hspec⟩ := L.exists_leSpec hLg hω σ
    have hag : ∀ v ∉ L.order.aux, assignOn L.order.aux ρ σ v = σ v := fun v hv =>
      assignOn_of_not_mem hv ρ σ
    have hagω := LoadedOrder.apply_agree hω hag
    obtain ⟨hdb', hc', hobj', -⟩ := LoadedOrder.fresh_agree hfresh hag
    obtain ⟨hdbω, hcω, hobjω, -⟩ := LoadedOrder.fresh_agree hfresh hagω
    have hall : AllHold (assignOn L.order.aux ρ σ) (db₀ ++ gs) := fun e he =>
      (hdb' e he).2 (List.mem_append.1 he |>.elim (hdb e) (hgs e))
    obtain ⟨hcτ, hgsτ, hobjτ, hordτ⟩ := redOk_sound (σ := assignOn L.order.aux ρ σ)
      (fun e he => hall e (List.mem_append_left _ he))
      (fun e he => hall e (List.mem_append_right _ he))
      (by rw [holds_negate, hc']; exact hc)
      (fun _ p hp => by
        obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hp
        exact (holds_normalize _ _).2 (hspec G hG)) hrun hok
    refine ⟨List.forall_mem_cons.2 ⟨(holds_normalize _ c).2 (hcω.1 hcτ),
      fun e he => (hdbω e (List.mem_append_right _ he)).1 (hgsτ e he)⟩, ?_, fun L' hL' => ?_⟩
    · rw [← hobjω, ← hobj']; exact hobjτ
    · rw [Option.mem_def, Option.some.injEq] at hL'
      subst hL'
      rcases hordτ L rfl with hu | hg
      · unfold LoadedOrder.Le
        rw [LoadedOrder.vals_apply_of_untouched hu]
        exact hLg.le_refl σ
      · have := LoadedOrder.le_apply_of_holds hLg hspec hg
        unfold LoadedOrder.Le at this ⊢
        rwa [LoadedOrder.vals_apply_agree hLg hω hag, LoadedOrder.vals_agree hLg hag] at this
  · -- No scope, and the witness leaves the order alone.
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hneed
    obtain ⟨hs, hu⟩ := hneed
    obtain ⟨hc', hgs', hobj, -⟩ := redOk_sound hdb hgs hnegC (by simp [hs]) hrun hok
    refine ⟨List.forall_mem_cons.2 ⟨(holds_normalize _ c).2 hc', hgs'⟩, hobj, fun L' hL' => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hL'
    subst hL'
    unfold LoadedOrder.Le
    rw [LoadedOrder.vals_apply_of_untouched hu]
    exact hLg.le_refl σ

/-- **The redundance check is sound**: an assignment `σ` satisfying the database is either one
satisfying `C` too, or `σ ∘ ω` satisfies the database and `C`; either way, the objective does not
increase. -/
theorem redCheck_sound {σ : ℕ → Bool} {obj : Option Objective} {db₀ : List (ℕ × PBConstr)}
    {n n' : ℕ} {c : PBConstr} {ω : Witness} {items : List RedItem} {qed : Option ℕ}
    (hdb : AllHold σ db₀) (h : redCheck obj db₀ n c ω items qed = some n') :
    ∃ τ, AllHold τ ((n', c.normalize) :: db₀) ∧ objValue obj τ ≤ objValue obj σ := by
  obtain ⟨τ, -, hτ, hle, -⟩ := redCheckOn_sound (by simp) hdb hdb h
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
    obtain ⟨-, hp⟩ := runGoals_top hcore hrun
    replace hp := hp.visible (scopeHolds_noScope σ false)
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
    {ord : Option LoadedOrder} {db₀ gs : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr}
    {ω : Witness} {items : List RedItem} {qed : Option ℕ}
    (h : redCheckP pres obj ord db₀ gs n c ω items qed = some n') :
    presFree pres ω = true ∧ redCheckOn obj ord db₀ gs n c ω items qed = some n' := by
  unfold redCheckP at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

/-- Two assignments have the same projection to `P` exactly when they agree on `P`. -/
theorem proj_eq_iff {P : List ℕ} {σ τ : ℕ → Bool} : proj P σ = proj P τ ↔ ∀ v ∈ P, σ v = τ v :=
  List.map_inj_left

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

/-! ### Soundness of order definitions -/

/-- **The check of `#` goals is sound**: every goal holds under every solution of the
premises. -/
private theorem hashGoalsCheck_sound {σ : ℕ → Bool} {db : List (ℕ × PBConstr)} {n n' : ℕ}
    {gs : List PBConstr} {p : OrderProof} (hdb : AllHold σ db)
    (h : hashGoalsCheck db n gs p = some n') : ∀ G ∈ gs, G.Holds σ := by
  unfold hashGoalsCheck at h
  split at h
  · cases h
  rename_i db' n'' proved hrun
  obtain ⟨hall, hp⟩ := runGoals_top hdb hrun
  replace hp := hp.visible (scopeHolds_noScope σ false)
  split at h
  · rename_i hok
    intro G hG
    cases hq : p.qed with
    | some q => simp [hq, hashGoalsOk, hall.not_namesContra] at hok
    | none =>
      simp only [hq, hashGoalsOk, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
      rcases hok G hG with h0 | hpr
      · exact holds_of_normalize_degree_eq_zero h0
      · exact hp.holds hpr
  · cases h

private theorem holds_orLit (σ : ℕ → Bool) (l : Literal ℕ) (c : PBConstr) :
    (orLit l c).Holds σ ↔ Literal.eval σ l = true ∨ c.Holds σ := by
  unfold orLit Holds
  simp only [lhs_cons, termVal]
  cases Literal.eval σ l
  · simp
  · simp only [Bool.toNat_true, mul_one, true_or, iff_true]
    omega

/-- **The goals of a change of the preserved set are sound**: the variables of `C` (normalized)
are preserved and are not `x`, and on every solution of the core set, `x` holds exactly when `C`
does. -/
theorem presChangeCheck_sound {core : List (ℕ × PBConstr)} {n n' : ℕ} {P : List ℕ} {x : ℕ}
    {c : PBConstr} {items : List RedItem} (h : presChangeCheck core n P x c items = some n') :
    (∀ t ∈ c.normalize.terms, termVar t ∈ P ∧ termVar t ≠ x) ∧
      ∀ τ, AllHold τ core → (τ x = true ↔ c.Holds τ) := by
  unfold presChangeCheck at h
  split at h
  · rename_i hv
    refine ⟨fun t ht => by simpa using List.all_eq_true.1 hv t ht, fun τ hτ => ?_⟩
    have hg := hashGoalsCheck_sound hτ h
    have h1 := (holds_orLit τ _ _).1 (hg (orLit (x, false) c.normalize) (by simp [presGoals]))
    have h2 := (holds_orLit τ _ _).1 (hg (orLit (x, true) c.negate) (by simp [presGoals]))
    simp only [Literal.eval, holds_normalize, holds_negate] at h1 h2
    cases hx : τ x <;> simp_all
  · cases h

/-- Assigning `ks₁ ++ ks₂` the values `bs₁ ++ bs₂` assigns `ks₁` the values `bs₁` first. -/
private theorem assignOn_append {ks₁ bs₁ : List _} (h : ks₁.length = bs₁.length)
    (ks₂ : List ℕ) (bs₂ : List Bool) (d : ℕ → Bool) :
    assignOn (ks₁ ++ ks₂) (bs₁ ++ bs₂) d = assignOn ks₁ bs₁ (assignOn ks₂ bs₂ d) := by
  funext j
  induction ks₁ generalizing bs₁ with
  | nil => cases bs₁ with
    | nil => rfl
    | cons => simp at h
  | cons k ks ih =>
    cases bs₁ with
    | nil => simp at h
    | cons b bs =>
      simp only [List.cons_append, assignOn]
      split
      · rfl
      · exact ih (by simpa using h)

/-- At a variable where two default assignments agree, so do their assignments of `ks`. -/
private theorem assignOn_congr_at {ks : List ℕ} {bs : List Bool} {d d' : ℕ → Bool} {j : ℕ}
    (h : d j = d' j) : assignOn ks bs d j = assignOn ks bs d' j := by
  induction ks generalizing bs with
  | nil => cases bs <;> exact h
  | cons k ks ih =>
    cases bs with
    | nil => exact h
    | cons b bs =>
      simp only [assignOn]
      split
      · rfl
      · exact ih

/-- The values of the variables of an order at `O.inst x y ρ`. -/
private theorem Order.map_inst {O : Order} (hnd : O.vars.Nodup) {x y ρ : List Bool}
    (hx : x.length = O.left.length) (hy : y.length = O.right.length)
    (hρ : ρ.length = O.aux.length) :
    O.left.map (O.inst x y ρ) = x ∧ O.right.map (O.inst x y ρ) = y ∧
      O.aux.map (O.inst x y ρ) = ρ := by
  have he : O.inst x y ρ = assignOn O.vars (x ++ y ++ ρ) fun _ => false := by
    rw [Order.inst, Order.vars, assignOn_append (by simp [hx, hy]), assignOn_append hx.symm]
  have hm := map_assignOn hnd (bs := x ++ y ++ ρ) (by simp [Order.vars, hx, hy, hρ])
    fun _ => false
  rw [← he, Order.vars, List.map_append, List.map_append] at hm
  obtain ⟨h₁, h₃⟩ := List.append_inj hm (by simp [hx, hy])
  obtain ⟨h₁, h₂⟩ := List.append_inj h₁ (by simp [hx])
  exact ⟨h₁, h₂, h₃⟩

/-- Off the auxiliary variables, `O.inst x y ρ` does not depend on `ρ`. -/
private theorem Order.inst_agree (O : Order) (x y ρ ρ' : List Bool) {v : ℕ} (hv : v ∉ O.aux) :
    O.inst x y ρ v = O.inst x y ρ' v := by
  unfold Order.inst
  refine assignOn_congr_at (assignOn_congr_at ?_)
  rw [assignOn_of_not_mem hv, assignOn_of_not_mem hv]

/-- A witness that sets none of the variable `v` leaves its value alone. -/
private theorem Witness.apply_of_forall_ne {ω : Witness} {v : ℕ} (h : ∀ e ∈ ω, e.1 ≠ v)
    (σ : ℕ → Bool) : Witness.apply σ ω v = σ v := by
  have hfind : Witness.find ω v = none := by
    simp only [Witness.find, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq]
    exact h
  simp [Witness.apply, hfind]

/-- **A checked specification derivation is sound**: if every assignment agrees, off the
auxiliary variables, with a solution of the database `db`, then every assignment agrees, off them,
with a solution of `db` and of the derived constraints `cs`. Each `red` step repairs a solution by
a witness that sets only auxiliary variables (CakePB's `check_spec_is_spec`). -/
private theorem Order.specCheckFrom_sound {O : Order} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (cs : List PBConstr) (ps : List SpecStep),
      O.specCheckFrom db n cs ps = true →
      (∀ σ : ℕ → Bool, ∃ σ' : ℕ → Bool, (∀ v ∉ O.aux, σ' v = σ v) ∧ AllHold σ' db) →
      ∀ σ : ℕ → Bool, ∃ σ' : ℕ → Bool, (∀ v ∉ O.aux, σ' v = σ v) ∧ AllHold σ' db ∧
        ∀ c ∈ cs, c.Holds σ'
  | _, _, [], [], _, h, σ => by
    obtain ⟨σ', h₁, h₂⟩ := h σ
    exact ⟨σ', h₁, h₂, by simp⟩
  | db, n, c :: cs, p :: ps, hchk, h, σ => by
    simp only [Order.specCheckFrom, Bool.and_eq_true, List.all_eq_true] at hchk
    obtain ⟨hsupp, hchk⟩ := hchk
    split at hchk
    · rename_i n' hred
      generalize (if p.sub.isSome = true then n' else n) = m at hchk
      have hstep : ∀ σ : ℕ → Bool, ∃ σ' : ℕ → Bool, (∀ v ∉ O.aux, σ' v = σ v) ∧
          AllHold σ' ((m, c.normalize) :: db) := by
        intro σ
        obtain ⟨σ₁, hag₁, h₁⟩ := h σ
        obtain ⟨τ, hτ, hall, -⟩ := redCheckOn_sound (by simp) h₁ h₁ hred
        refine ⟨τ, ?_, List.forall_mem_cons.2 ⟨(List.forall_mem_cons.1 hall).1,
          (List.forall_mem_cons.1 hall).2⟩⟩
        rcases hτ with rfl | rfl
        · exact hag₁
        · intro v hv
          rw [Witness.apply_of_forall_ne (fun e he hev => hv (by
            rw [← hev]; simpa using hsupp e he)) σ₁]
          exact hag₁ v hv
      obtain ⟨σ', hag, hall, hcs⟩ := Order.specCheckFrom_sound _ _ cs ps hchk hstep σ
      exact ⟨σ', hag, fun e he => hall e (List.mem_cons_of_mem _ he),
        List.forall_mem_cons.2 ⟨(holds_normalize _ c).1 (hall _ List.mem_cons_self), hcs⟩⟩
    · cases hchk
  | _, _, [], _ :: _, h, _, _ => by simp [Order.specCheckFrom] at h
  | _, _, _ :: _, [], h, _, _ => by simp [Order.specCheckFrom] at h

/-- **A passing `def_order` check gives a good order**: a specification, and a preorder on the
vectors as long as its left variables (and so, loaded over as many literals, a preorder on
assignments, `Cslib.Logic.PL.VeriPB.LoadedOrder.isPreorder`). -/
theorem Order.good_of_defCheck {O : Order} {sp : List SpecStep} {w : TransVars}
    {trans refl : OrderProof} (h : O.defCheck sp w trans refl = true) : O.Good := by
  unfold Order.defCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hwf, hsp⟩, h⟩ := h
  split at h
  swap
  · cases h
  rename_i n htr
  obtain ⟨hlr, hnd, -⟩ := Order.wellFormed_iff.1 hwf
  -- The specification: every assignment agrees off `a` with a solution of it.
  have hspec : ∀ x y : List Bool, ∃ ρ : List Bool, ρ.length = O.aux.length ∧
      ∀ S ∈ O.spec, S.Holds (O.inst x y ρ) := by
    intro x y
    obtain ⟨σ', hag, -, hS⟩ := Order.specCheckFrom_sound [] 1 O.spec sp hsp
      (fun σ => ⟨σ, fun _ _ => rfl, by simp [AllHold]⟩) (O.inst x y [])
    refine ⟨O.aux.map σ', by simp, fun S hS' => (holds_congr fun t ht => ?_).1 (hS S hS')⟩
    have hv := (Order.wellFormed_iff.1 hwf).2.2 S (List.mem_append_left _ hS') t ht
    by_cases ha : termVar t ∈ O.aux
    · have hd := (List.nodup_append.1 hnd).2.2
      have hl : termVar t ∉ O.left := fun hl =>
        hd _ (List.mem_append_left _ hl) _ ha rfl
      have hr : termVar t ∉ O.right := fun hr =>
        hd _ (List.mem_append_right _ hr) _ ha rfl
      unfold Order.inst
      rw [assignOn_of_not_mem hl, assignOn_of_not_mem hr, assignOn_map_self ha]
    · rw [O.inst_agree x y (O.aux.map σ') [] ha]
      exact hag _ ha
  refine ⟨hwf, hspec, fun x hx => ?_, fun x y z hx hy hz hxy hyz => ?_⟩
  · -- Reflexivity, from the goals `O⪯(u, u, a)` at `O.inst x x ρ` for `S⪯(x, x, ρ)`.
    obtain ⟨ρ, hρ, hS⟩ := hspec x x
    obtain ⟨hu, -, ha⟩ := Order.map_inst hnd hx (by rw [hx, hlr]) hρ
    unfold Order.reflCheck at h
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.1 h
    have hprem : ∀ G ∈ O.specC (posVals O.left) (posVals O.left) (posVals O.aux),
        G.Holds (O.inst x x ρ) := by
      rw [Order.holds_specC hwf (by simp [posVals]) (by simp [posVals, hlr]) (by simp [posVals]),
        map_eval_posVals, map_eval_posVals, hu, ha]
      exact hS
    have hg := hashGoalsCheck_sound (σ := O.inst x x ρ)
      (allHold_pushAll [] n _ (by simp [AllHold]) fun p hp => by
        obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hp
        exact (holds_normalize _ _).2 (hprem G hG)) hn'
    rw [Order.holds_instC hwf (by simp [posVals]) (by simp [posVals, hlr]) (by simp [posVals]),
      map_eval_posVals, map_eval_posVals, hu, ha] at hg
    exact ⟨ρ, hρ, List.forall_mem_append.2 ⟨hS, hg⟩⟩
  · -- Transitivity, from the goals `O⪯(u, w, c)` at the assignment giving `u`, `v`, `a`, `w`,
    -- `b`, `c` the values `x`, `y`, `ρ₁`, `z`, `ρ₂`, `ρ₃`.
    obtain ⟨ρ₁, hρ₁, h₁⟩ := hxy
    obtain ⟨ρ₂, hρ₂, h₂⟩ := hyz
    obtain ⟨ρ₃, hρ₃, h₃⟩ := hspec x z
    unfold Order.transCheck at htr
    split at htr
    swap
    · cases htr
    rename_i hw
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨hwl, hb⟩, hc⟩, hK⟩ := hw
    have hm := map_assignOn hK (bs := x ++ y ++ ρ₁ ++ z ++ ρ₂ ++ ρ₃)
      (by simp [Order.vars, hx, hy, hz, hρ₁, hρ₂, hρ₃, hwl, hb, hc]; omega) fun _ => false
    generalize assignOn _ _ _ = γ at hm
    simp only [Order.vars, List.map_append] at hm
    obtain ⟨hm, hcm⟩ := List.append_inj hm (by simp [hx, hy, hz, hρ₁, hρ₂, hwl, hb]; omega)
    obtain ⟨hm, hbm⟩ := List.append_inj hm (by simp [hx, hy, hz, hρ₁, hwl]; omega)
    obtain ⟨hm, hwm⟩ := List.append_inj hm (by simp [hx, hy, hρ₁]; omega)
    obtain ⟨hm, ham⟩ := List.append_inj hm (by simp [hx, hy]; omega)
    obtain ⟨hum, hvm⟩ := List.append_inj hm (by simp [hx])
    have hl : ∀ {a : List WVal}, a = posVals O.left ∨ a = posVals O.right ∨ a = posVals w.right →
        a.length = O.left.length := by
      rintro a (rfl | rfl | rfl) <;> simp [posVals, hlr, hwl]
    have hprem : ∀ G ∈ O.specC (posVals O.left) (posVals O.right) (posVals O.aux) ++
        O.specC (posVals O.right) (posVals w.right) (posVals w.aux₁) ++
        O.specC (posVals O.left) (posVals w.right) (posVals w.aux₂) ++
        O.instC (posVals O.left) (posVals O.right) (posVals O.aux) ++
        O.instC (posVals O.right) (posVals w.right) (posVals w.aux₁), G.Holds γ := by
      simp only [List.forall_mem_append]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [Order.holds_specC hwf (hl (.inl rfl)) (hlr ▸ hl (.inr (.inl rfl))) (by simp [posVals]),
          map_eval_posVals, map_eval_posVals, map_eval_posVals, hum, hvm, ham]
        exact fun S hS => h₁ S (List.mem_append_left _ hS)
      · rw [Order.holds_specC hwf (hl (.inr (.inl rfl))) (hlr ▸ hl (.inr (.inr rfl)))
          (by simp [posVals, hb]), map_eval_posVals, map_eval_posVals, map_eval_posVals, hvm, hwm,
          hbm]
        exact fun S hS => h₂ S (List.mem_append_left _ hS)
      · rw [Order.holds_specC hwf (hl (.inl rfl)) (hlr ▸ hl (.inr (.inr rfl)))
          (by simp [posVals, hc]), map_eval_posVals, map_eval_posVals, map_eval_posVals, hum, hwm,
          hcm]
        exact h₃
      · rw [Order.holds_instC hwf (hl (.inl rfl)) (hlr ▸ hl (.inr (.inl rfl))) (by simp [posVals]),
          map_eval_posVals, map_eval_posVals, map_eval_posVals, hum, hvm, ham]
        exact fun D hD => h₁ D (List.mem_append_right _ hD)
      · rw [Order.holds_instC hwf (hl (.inr (.inl rfl))) (hlr ▸ hl (.inr (.inr rfl)))
          (by simp [posVals, hb]), map_eval_posVals, map_eval_posVals, map_eval_posVals, hvm, hwm,
          hbm]
        exact fun D hD => h₂ D (List.mem_append_right _ hD)
    have hg := hashGoalsCheck_sound (allHold_initDb hprem) htr
    rw [Order.holds_instC hwf (hl (.inl rfl)) (hlr ▸ hl (.inr (.inr rfl)))
      (by simp [posVals, hc]), map_eval_posVals, map_eval_posVals, map_eval_posVals, hum, hwm,
      hcm] at hg
    exact ⟨ρ₃, hρ₃, List.forall_mem_append.2 ⟨h₃, hg⟩⟩

/-! ### Soundness of `dom` -/

private theorem presFree_of_domCheck {pres : Option (List ℕ)} {obj : Option Objective}
    {L : LoadedOrder} {db core : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr} {ω : Witness}
    {items : List RedItem} {qed : Option ℕ}
    (h : domCheck pres obj L db core n c ω items qed = some n') : presFree pres ω = true := by
  unfold domCheck at h
  split at h
  · rename_i hif
    exact (Bool.and_eq_true _ _ ▸ hif).1
  · cases h

/-- **The dominance check is sound**: an assignment `σ` satisfying the database and its core set
but not `C` is mapped by the witness to an assignment satisfying the core set, strictly below `σ`
in the loaded order, and with no larger objective value. The goals proved in a scope hold because
the auxiliary variables are fresh: `σ` can be given values of them satisfying `S⪯(z↾ω, z, a)`,
and, were `σ ⪯ σ ∘ ω`, values satisfying `S⪯(z, z↾ω, a)` and `O⪯(z, z↾ω, a)` (CakePB's
`good_aspo_dominance`). -/
theorem domCheck_sound {σ : ℕ → Bool} {pres : Option (List ℕ)} {obj : Option Objective}
    {L : LoadedOrder} {db core : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr} {ω : Witness}
    {items : List RedItem} {qed : Option ℕ} (hL : L.Good) (hdb : AllHold σ db)
    (hcore : AllHold σ core) (hc : ¬ c.Holds σ)
    (h : domCheck pres obj L db core n c ω items qed = some n') :
    AllHold (Witness.apply σ ω) core ∧ L.Le (Witness.apply σ ω) σ ∧
      ¬ L.Le σ (Witness.apply σ ω) ∧ objValue obj (Witness.apply σ ω) ≤ objValue obj σ := by
  unfold domCheck at h
  split at h
  swap
  · cases h
  rename_i hif
  have hfresh := (Bool.and_eq_true _ _ ▸ hif).2
  split at h
  · cases h
  rename_i db' n'' proved hrun
  split at h
  swap
  · cases h
  rename_i hok
  have hω := (LoadedOrder.fresh_agree hfresh (σ := σ) fun _ _ => rfl).2.2.2
  -- At every assignment agreeing with `σ` off the auxiliary variables, the run refutes `proved`.
  have hagree : ∀ ρ : List Bool, AllHold (assignOn L.order.aux ρ σ) db ∧
      AllHold (assignOn L.order.aux ρ σ) core ∧ c.negate.Holds (assignOn L.order.aux ρ σ) ∧
      RefutedIn (domScope L ω) (assignOn L.order.aux ρ σ) proved := by
    intro ρ
    obtain ⟨hdb', hc', -⟩ := LoadedOrder.fresh_agree hfresh
      (fun v hv => assignOn_of_not_mem hv ρ σ)
    have hall : AllHold (assignOn L.order.aux ρ σ) (db ++ core) := fun e he =>
      (hdb' e he).2 (List.mem_append.1 he |>.elim (hdb e) (hcore e))
    have hneg : c.negate.Holds (assignOn L.order.aux ρ σ) := by
      rw [holds_negate, hc']; exact hc
    obtain ⟨-, hp⟩ := runGoals_top
      (List.forall_mem_cons.2 ⟨hneg, fun e he => hall e (List.mem_append_left _ he)⟩) hrun
    exact ⟨fun e he => hall e (List.mem_append_left _ he),
      fun e he => hall e (List.mem_append_right _ he), hneg, hp⟩
  cases qed with
  | some q =>
    have hneg : AllHold σ ((n, c.negate) :: db) :=
      List.forall_mem_cons.2 ⟨(holds_negate σ c).2 hc, hdb⟩
    obtain ⟨hall, -⟩ := runGoals_top hneg hrun
    simp [domOk, hall.not_namesContra] at hok
  | none =>
  simp only [domOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hgeq, hle⟩, hsub⟩ := hok
  -- The goals other than `#N + 1`, at values of the auxiliary variables satisfying
  -- `S⪯(z↾ω, z, a)`.
  obtain ⟨ρ, -, hspec⟩ := L.exists_leSpec hL hω σ
  have hag : ∀ v ∉ L.order.aux, assignOn L.order.aux ρ σ v = σ v := fun v hv =>
    assignOn_of_not_mem hv ρ σ
  obtain ⟨hdb', hcore', hneg', hp⟩ := hagree ρ
  have hp' := hp.visible (b := false) fun S hS p hp => by
    simp only [domScope, Option.some.injEq] at hS
    subst hS
    obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hp
    exact (holds_normalize _ _).2 (hspec G hG)
  obtain ⟨hcoreτ, hobjτ⟩ := substCovered_sound hdb' hcore' hp' hneg' hsub
  obtain ⟨hcoreω, -, hobjω, -⟩ := LoadedOrder.fresh_agree hfresh (LoadedOrder.apply_agree hω hag)
  obtain ⟨-, -, hobj', -⟩ := LoadedOrder.fresh_agree hfresh hag
  refine ⟨fun e he => (hcoreω e (List.mem_append_right _ he)).1 (hcoreτ e he), ?_, fun hge => ?_,
    by rw [← hobjω, ← hobj']; exact hobjτ⟩
  · have := LoadedOrder.le_apply_of_holds hL hspec fun G hG => goalCovered_holds hdb' hp' hneg'
      (hle G hG)
    unfold LoadedOrder.Le at this ⊢
    rwa [LoadedOrder.vals_apply_agree hL hω hag, LoadedOrder.vals_agree hL hag] at this
  · -- Goal `#N + 1`, at values of the auxiliary variables satisfying `S⪯(z, z↾ω, a)` and
    -- `O⪯(z, z↾ω, a)`.
    obtain ⟨ρ', -, hG⟩ := LoadedOrder.exists_ge_of_le hL hω hge
    obtain ⟨-, -, -, hp''⟩ := hagree ρ'
    have hnorm : ∀ G ∈ L.geSpec ω ++ L.geGoals ω, G.normalize.Holds (assignOn L.order.aux ρ' σ) :=
      fun G hG' => (holds_normalize _ _).2 (hG G hG')
    have hp₁ := hp''.visible (b := true) fun S hS p hp => by
      simp only [domScope, Option.some.injEq] at hS
      subst hS
      obtain ⟨G', hGm, rfl⟩ := List.mem_map.1 hp
      exact hnorm G' (List.mem_append_left _ hGm)
    refine hp₁ _ (List.contains_iff_mem.1 hgeq) fun G hG' => ?_
    obtain ⟨G', hGm, rfl⟩ := List.mem_map.1 hG'
    exact hnorm G' (List.mem_append_right _ hGm)

/-- **CakePB's `sat_obj_po`** for the preserved set `pres`, the loaded order `L` and the
objective `obj`: every solution `τ` of `C` gives a solution of `D` below `τ` in the order, of no
larger objective value, and with the same projection to the preserved set. -/
@[expose]
def SatObjPo (pres : Option (List ℕ)) (L : LoadedOrder) (obj : Option Objective)
    (C D : List (ℕ × PBConstr)) : Prop :=
  ∀ τ, AllHold τ C → ∃ τ', AllHold τ' D ∧ L.Le τ' τ ∧ objValue obj τ' ≤ objValue obj τ ∧
    ∀ P ∈ pres, proj P τ' = proj P τ

/-- `C` gives back itself, by reflexivity. -/
theorem SatObjPo.refl {pres : Option (List ℕ)} {L : LoadedOrder} {obj : Option Objective}
    {C D : List (ℕ × PBConstr)} (hL : L.Good) (h : ∀ τ, AllHold τ C → AllHold τ D) :
    SatObjPo pres L obj C D := fun τ hτ => ⟨τ, h τ hτ, hL.le_refl τ, le_rfl, fun _ _ => rfl⟩

/-- **Dominance-based strengthening is sound** (§5.4.2; CakePB's `dominance_conf_valid`): if every
solution of the core set `C` gives a solution of the database `D` below it, and the witness maps
every solution of `D` violating `c` to a solution of `C` strictly below it in the loaded order,
with no larger objective value, then every solution of `C` gives a solution of `D` and `c` below
it. The witness is applied repeatedly; this terminates because the strict part of the order is
well founded (`Cslib.Logic.PL.VeriPB.LoadedOrder.wellFounded`). -/
theorem SatObjPo.dom {pres : Option (List ℕ)} {L : LoadedOrder} {obj : Option Objective}
    {C D : List (ℕ × PBConstr)} {c : PBConstr} {ω : Witness} (m : ℕ) (hL : L.Good)
    (h : SatObjPo pres L obj C D) (hfree : presFree pres ω = true)
    (hdom : ∀ σ, AllHold σ D → ¬ c.Holds σ → AllHold (Witness.apply σ ω) C ∧
      L.Le (Witness.apply σ ω) σ ∧ ¬ L.Le σ (Witness.apply σ ω) ∧
      objValue obj (Witness.apply σ ω) ≤ objValue obj σ) :
    SatObjPo pres L obj C ((m, c.normalize) :: D) := by
  intro τ
  induction τ using (L.wellFounded hL).induction with
  | _ τ ih =>
  intro hτ
  obtain ⟨τ₁, h₁, hle₁, hobj₁, hp₁⟩ := h τ hτ
  by_cases hc : c.Holds τ₁
  · exact ⟨τ₁, List.forall_mem_cons.2 ⟨(holds_normalize _ _).2 hc, h₁⟩, hle₁, hobj₁, hp₁⟩
  obtain ⟨h₂, hle₂, hnle₂, hobj₂⟩ := hdom τ₁ h₁ hc
  have hlt : L.Le (Witness.apply τ₁ ω) τ ∧ ¬ L.Le τ (Witness.apply τ₁ ω) :=
    ⟨hL.le_trans hle₂ hle₁, fun h' => hnle₂ (hL.le_trans hle₁ h')⟩
  obtain ⟨τ₃, h₃, hle₃, hobj₃, hp₃⟩ := ih _ hlt h₂
  exact ⟨τ₃, h₃, hL.le_trans hle₃ hlt.1, hobj₃.trans (hobj₂.trans hobj₁), fun P hP =>
    (hp₃ P hP).trans ((proj_apply_of_presFree hfree τ₁ P hP).trans (hp₁ P hP))⟩

/-! ### The numbering only advances -/

private theorem le_pushAll :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (ps : List PBConstr), n ≤ (pushAll db n ps).2
  | _, _, [] => le_rfl
  | _, n, _ :: ps => (Nat.le_succ n).trans (le_pushAll _ (n + 1) ps)

mutual

private theorem runItem_le {goal : GoalId → Option (List PBConstr)} :
    ∀ (scope : Bool → Option (List PBConstr)) (cur : Option Bool) (db : List (ℕ × PBConstr))
      (n : ℕ) (it : RedItem) (proved : List Tagged) (db' : List (ℕ × PBConstr))
      (n' : ℕ) (proved' : List Tagged),
      runItem goal scope cur db n it proved = some (db', n', proved') → n ≤ n'
  | _, _, db, n, .step s, proved, db', n', proved', h => by
    simp only [runItem, Option.map_eq_some_iff] at h
    obtain ⟨⟨db₁, n₁⟩, h₁, h⟩ := h
    simp only [Prod.mk.injEq] at h
    exact h.2.1 ▸ runStep_le _ _ _ _ _ h₁
  | _, _, db, n, .goal g sub q, proved, db', n', proved', h => by
    simp only [runItem] at h
    split at h
    · cases h
    · rename_i ps _
      split at h
      · rename_i db₂ n₂ h₂
        simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at h
        exact h.2.2.1 ▸ (le_pushAll db n ps).trans (runSteps_le _ _ sub _ _ h₂)
      · cases h
  | scope, cur, db, n, .scope b inner, proved, db', n', proved', h => by
    simp only [runItem] at h
    split at h
    · split at h
      · cases h
      · rename_i S _
        split at h
        · rename_i db₂ n₂ proved₂ h₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.1 ▸ (le_pushAll db n S).trans
            (runGoals_le _ (some b) _ _ inner proved db₂ n₂ proved₂ h₂)
        · cases h
    · cases h

private theorem runGoals_le {goal : GoalId → Option (List PBConstr)} :
    ∀ (scope : Bool → Option (List PBConstr)) (cur : Option Bool) (db : List (ℕ × PBConstr))
      (n : ℕ) (items : List RedItem) (proved : List Tagged) (db' : List (ℕ × PBConstr))
      (n' : ℕ) (proved' : List Tagged),
      runGoals goal scope cur db n items proved = some (db', n', proved') → n ≤ n'
  | _, _, db, n, [], proved, db', n', proved', h => by
    simp only [runGoals, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.1 ▸ le_rfl
  | scope, cur, db, n, it :: items, proved, db', n', proved', h => by
    simp only [runGoals] at h
    split at h
    · rename_i db₁ n₁ proved₁ h₁
      exact (runItem_le scope cur db n it proved db₁ n₁ proved₁ h₁).trans
        (runGoals_le scope cur db₁ n₁ items proved₁ db' n' proved' h)
    · cases h

end

private theorem redCheckP_le {pres : Option (List ℕ)} {obj : Option Objective}
    {ord : Option LoadedOrder} {db₀ gs : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr}
    {ω : Witness} {items : List RedItem} {q : Option ℕ}
    (h : redCheckP pres obj ord db₀ gs n c ω items q = some n') : n ≤ n' := by
  simp only [redCheckP, redCheckOn, Option.ite_none_right_eq_some] at h
  obtain ⟨-, h⟩ := h
  split at h
  · cases h
  · rename_i db' n₁ proved h₁
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    exact h.2 ▸ (Nat.le_succ n).trans (runGoals_le _ _ _ _ _ _ _ _ _ h₁)

private theorem domCheck_le {pres : Option (List ℕ)} {obj : Option Objective} {L : LoadedOrder}
    {db core : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr} {ω : Witness}
    {items : List RedItem} {q : Option ℕ}
    (h : domCheck pres obj L db core n c ω items q = some n') : n ≤ n' := by
  simp only [domCheck, Option.ite_none_right_eq_some] at h
  obtain ⟨-, h⟩ := h
  split at h
  · cases h
  · rename_i db' n₁ proved h₁
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    exact h.2 ▸ (Nat.le_succ n).trans (runGoals_le _ _ _ _ _ _ _ _ _ h₁)

private theorem objuCheck_le {core : List (ℕ × PBConstr)} {n n' : ℕ} {f f' : Objective}
    {items : List RedItem} (h : objuCheck core n f f' items = some n') : n ≤ n' := by
  simp only [objuCheck] at h
  split at h
  · rename_i db' n₁ proved h₁
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    exact h.2 ▸ runGoals_le _ _ _ _ _ _ _ _ _ h₁
  · cases h

private theorem presChangeCheck_le {core : List (ℕ × PBConstr)} {n n' : ℕ} {P : List ℕ}
    {x : ℕ} {c : PBConstr} {items : List RedItem}
    (h : presChangeCheck core n P x c items = some n') : n ≤ n' := by
  simp only [presChangeCheck, hashGoalsCheck, Option.ite_none_right_eq_some] at h
  obtain ⟨-, h⟩ := h
  split at h
  · cases h
  · rename_i db' n₁ proved h₁
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    exact h.2 ▸ runGoals_le _ _ _ _ _ _ _ _ _ h₁

/-- The number that a `red` or `dom` step gives its constraint, `n'` after a subproof and `n`
without one, is at least `n`. -/
private theorem le_ite_of_le {b : Bool} {n n' : ℕ} (h : n ≤ n') : n ≤ if b then n' else n := by
  split
  · exact h
  · exact le_rfl

/-! ### The invariants -/

private theorem holds_of_solves_normalize {ρ : List (Literal ℕ)} {F : List PBConstr}
    (h : solves ρ (F.map normalize) = true) : ∀ c ∈ F, c.Holds (assignOf ρ) := fun c hc =>
  (holds_normalize _ c).1 (holds_of_solves h (List.mem_map_of_mem hc))

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
    (hd : st.delIds.contains e.1 = false) : e ∈ db' :=
  (runStep_effect _ _ _ _ _ h).mem he fun _ hst => by simpa [hst, Step.delIds] using hd

/-- **The core invariant** of a state for the formula `F` and the input objective `obj`: CakePB's
`valid_conf`, the `chk` part of `check_csteps_correct`, and its `id_ok`. -/
structure Inv (F : List PBConstr) (obj : Option Objective) (s : State) : Prop where
  /-- The core set is part of the database. -/
  sub : ∀ e ∈ s.core, e ∈ s.db
  /-- In strengthening-to-core mode, the core set implies the database (§5.6). -/
  imp : s.tcb = true → ∀ τ, AllHold τ s.core → AllHold τ s.db
  /-- While no unchecked deletion has happened, every solution of the core set gives a solution
  of `F` whose input objective value is at most its current objective value: CakePB's backward
  `bimp_obj`. The projections are in the counting injections
  (`Cslib.Logic.PL.VeriPB.InjInv.bwd`). -/
  chk : s.chk = true → ∀ τ, AllHold τ s.core →
    ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ objValue s.obj τ
  /-- The bound `bound` is at least the input objective value of a solution of `F`. -/
  wit : ∀ v ∈ s.bound, ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ v
  /-- The numbers of the database, and so of the core set, are distinct and below `next`
  (CakePB's `id_ok`). -/
  ids : IdOk s.db s.next

theorem inv_init (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) :
    Inv F obj (State.init F obj pres) where
  sub _ he := he
  imp h := by simp [State.init] at h
  chk _ τ hτ := ⟨τ, holds_of_allHold_initDb hτ, le_rfl⟩
  wit v hv := by simp [State.init] at hv
  ids := idOk_initDb F

/-- Under the invariant, every constraint of the core set with the number of `lookup s.core i` is
that constraint: the core set is part of the database, whose numbers are distinct. -/
private theorem Inv.core_all {F : List PBConstr} {obj : Option Objective} {s : State} {i : ℕ}
    {c : PBConstr} (hs : Inv F obj s) (hc : lookup s.core i = some c) :
    s.core.all (fun e => e.1 != i || e.2 == c) = true := by
  unfold lookup at hc
  obtain ⟨e₀, he₀, rfl⟩ := Option.map_eq_some_iff.1 hc
  have hi : e₀.1 = i := by simpa using List.find?_some he₀
  refine List.all_eq_true.2 fun e he => ?_
  by_cases hei : e.1 = i
  · have h₀ := hs.sub _ (List.mem_of_find?_eq_some he₀)
    rw [← hi] at hei
    rw [← Prod.mk.eta (p := e), hei] at he ⊢
    rw [← Prod.mk.eta (p := e₀)] at h₀
    simp [hs.ids.eq_of_mem (hs.sub _ he) h₀]
  · simp [hei]

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
    · obtain ⟨σ, hσ, hle⟩ := hs.chk hc _ fun e he =>
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
  ids := hs.ids.cons le_rfl c

/-- Asserting an objective value keeps the core invariant. -/
private theorem inv_improve {F : List PBConstr} {obj : Option Objective} {s : State}
    {f : Objective} {v : ℤ} (hs : Inv F obj s) : Inv F obj (s.improve f v) :=
  have h := inv_addCore (c := (f.improving v).normalize) hs
  ⟨h.sub, h.imp, h.chk, h.wit, h.ids⟩

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

/-- Adding a constraint derived by `red` or `dom` keeps the core invariant: the core set stays in
the database, grows only with it, and so keeps fewer solutions. -/
private theorem inv_addStrengthened {F : List PBConstr} {obj : Option Objective} {s : State}
    (hs : Inv F obj s) {m : ℕ} (hm : s.next ≤ m) (c : PBConstr) :
    Inv F obj (s.addStrengthened m c) := by
  unfold State.addStrengthened
  refine ⟨fun e he => ?_, fun ht τ hτ => ?_, fun hc τ hτ => ?_, hs.wit, hs.ids.cons hm _⟩
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

/-- **Each step keeps the core invariant**, if the loaded order, if any, is good
(`Cslib.Logic.PL.VeriPB.OrdInv`): a `red` step or a checked deletion proved in `scope leq` relies on
its specification. -/
theorem stepTop_inv {F : List PBConstr} {obj : Option Objective} {s s' : State} {t : TopStep}
    (hs : Inv F obj s) (hord : ∀ L ∈ s.order, L.Good) (h : stepTop F obj s t = some s') :
    Inv F obj s' := by
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
        refine ⟨fun e he => ?_, fun ht τ hτ => ?_, fun hc τ hτ => ?_, hs.wit,
          hs.ids.runStep hrun⟩
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
      exact inv_addStrengthened hs (le_ite_of_le (redCheckP_le hred)) c
    · cases h
  | sol ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i hρ
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hs.sub, hs.imp, hs.chk, wit_log hs hρ, hs.ids⟩
    · cases h
  | soli ρ =>
    simp only [stepTop] at h
    split at h
    · split at h
      · rename_i f hρ
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hρ
        exact inv_improve ⟨hs.sub, hs.imp, hs.chk, wit_log hs hρ.1, hs.ids⟩
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
        fun ht τ hτ => allHold_filter (hs.imp ht τ hτ) _, hs.chk, hs.wit, hs.ids.filter _⟩
    · cases h
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      refine ⟨fun e he => ?_, fun ht τ hτ => ?_, (fun hc => by cases hc), hs.wit,
        hs.ids.filter _⟩
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
            obtain ⟨τ', hτ', hall, hle, -⟩ :=
              redCheckOn_sound hord hτ hτ (redCheckOn_of_redCheckP hred).2
            exact ⟨τ', hτ', allHold_core_of_filter (hs.core_all hc) (fun e he => hall e
              (List.mem_cons_of_mem _ he)) ((holds_normalize _ _).1 (hall _ List.mem_cons_self)),
              hle⟩
          refine ⟨fun e he => ?_, fun ht τ hτ => ?_, fun hc τ hτ => ?_, hs.wit,
            (hs.ids.filter _).mono (le_ite_of_le (redCheckP_le hred))⟩
          · rw [List.mem_filter] at he ⊢
            exact ⟨hs.sub e he.1, he.2⟩
          · have hω : ω = [] := by
              rcases hok with hf | hω
              · simp [hf] at ht
              · exact List.isEmpty_iff.1 hω.1
            obtain ⟨τ', hτ', hall, -⟩ := hback τ hτ
            have : τ' = τ := by rcases hτ' with rfl | rfl <;> simp [hω, Witness.apply_nil]
            subst this
            exact allHold_filter (hs.imp ht τ' hall) _
          · obtain ⟨τ', hτ', hall, hle⟩ := hback τ hτ
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
        (List.mem_append_right _ he), hs.wit, hs.ids⟩
      rcases List.mem_append.1 he with he | he
      · exact (List.mem_filter.1 he).1
      · exact hs.sub e he
    · cases h
  | strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h
    · exact ⟨hs.sub, (fun h => by cases h), hs.chk, hs.wit, hs.ids⟩
    · exact ⟨fun _ he => he, fun _ _ hτ => hτ,
        fun hc τ hτ => hs.chk hc τ (allHold_mono hs.sub hτ), hs.wit, hs.ids⟩
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
        refine ⟨hs.sub, hs.imp, fun hc τ hτ => ?_, hs.wit, hs.ids.mono (objuCheck_le hobj)⟩
        obtain ⟨σ, hσ, hle⟩ := hs.chk hc τ hτ
        refine ⟨σ, hσ, ?_⟩
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
          ⟨hs.sub, hs.imp, hs.chk, wit_log hs hok.1.2, hs.ids⟩
        exact ⟨h.sub, h.imp, h.chk, h.wit, h.ids⟩
      · cases h
    · cases h
  | defOrder name O w tp rp =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨hs.sub, hs.imp, hs.chk, hs.wit, hs.ids⟩
    · cases h
  | loadOrder name z =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨fun _ he => he, fun _ _ hτ => hτ,
          fun hc τ hτ => hs.chk hc τ (allHold_mono hs.sub hτ), hs.wit, hs.ids⟩
      · cases h
    · cases h
  | unloadOrder =>
    simp only [stepTop, Option.some.injEq] at h
    subst h
    exact ⟨hs.sub, hs.imp, hs.chk, hs.wit, hs.ids⟩
  | presChange add x c sub =>
    simp only [stepTop] at h
    split at h
    · rename_i P hP
      split at h
      · rename_i n' hchk
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨hs.sub, hs.imp, hs.chk, hs.wit, hs.ids.mono (presChangeCheck_le hchk)⟩
      · cases h
    · cases h
  | epreserved _ | eordDef _ _ | eordLoaded _ _ | econstr _ _ =>
    obtain ⟨-, ⟨⟩⟩ := Option.ite_none_right_eq_some.1 h
    exact hs
  | dom c ω items q =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact inv_addStrengthened hs (le_ite_of_le (domCheck_le ‹_›)) c
      · cases h
    · cases h

/-! ### Monotonicity -/

/-- **The monotonicity facts** from the state `s` to the state `s'`, for the input formula `F` and
the input objective `obj`, as in CakePB's `check_csteps_correct`: the numbering only advances,
the bounds `dbound` and `bound` only decrease, `chk` is never restored, and the logged projections
only grow; without `chk`, they are frozen, and `bound` takes only its old values and input
objective values of solutions of `F`. CakePB freezes `bound` without `chk`; this checker still
lowers it for a logged solution that solves `F` (`Cslib.Logic.PL.VeriPB.State.log`). -/
structure Mono (F : List PBConstr) (obj : Option Objective) (s s' : State) : Prop where
  /-- The numbering only advances. -/
  next : s.next ≤ s'.next
  /-- The bound `dbound` only decreases. -/
  dbound : ∀ v ∈ s.dbound, ∃ v' ∈ s'.dbound, v' ≤ v
  /-- The bound `bound` only decreases. -/
  bound : ∀ v ∈ s.bound, ∃ v' ∈ s'.bound, v' ≤ v
  /-- `chk` is never restored. -/
  chk : s'.chk = true → s.chk = true
  /-- The logged projections only grow. -/
  logged : s.logged <:+ s'.logged
  /-- Without `chk`, the logged projections are frozen. -/
  logged_eq : s.chk = false → s'.logged = s.logged
  /-- Without `chk`, `bound` takes only its old values and input objective values of solutions of
  `F`. -/
  bound_input : s.chk = false → ∀ v ∈ s'.bound,
    v ∈ s.bound ∨ ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ = v

namespace Mono

variable {F : List PBConstr} {obj : Option Objective}

/-- No step at all. -/
theorem refl (s : State) : Mono F obj s s :=
  ⟨le_rfl, fun v hv => ⟨v, hv, le_rfl⟩, fun v hv => ⟨v, hv, le_rfl⟩, id, List.suffix_refl _,
    fun _ => rfl, fun _ _ hv => .inl hv⟩

/-- Steps in turn. -/
theorem trans {s₁ s₂ s₃ : State} (h₁ : Mono F obj s₁ s₂) (h₂ : Mono F obj s₂ s₃) :
    Mono F obj s₁ s₃ := by
  have hc : s₁.chk = false → s₂.chk = false := fun hc => Bool.eq_false_iff.2 fun h => by
    simpa [hc] using h₁.chk h
  refine ⟨h₁.next.trans h₂.next, fun v hv => ?_, fun v hv => ?_, h₁.chk ∘ h₂.chk,
    h₁.logged.trans h₂.logged, fun h => (h₂.logged_eq (hc h)).trans (h₁.logged_eq h),
    fun h v hv => (h₂.bound_input (hc h) v hv).elim (h₁.bound_input h v) .inr⟩
  · obtain ⟨v₂, hv₂, hle₂⟩ := h₁.dbound v hv
    obtain ⟨v₃, hv₃, hle₃⟩ := h₂.dbound v₂ hv₂
    exact ⟨v₃, hv₃, hle₃.trans hle₂⟩
  · obtain ⟨v₂, hv₂, hle₂⟩ := h₁.bound v hv
    obtain ⟨v₃, hv₃, hle₃⟩ := h₂.bound v₂ hv₂
    exact ⟨v₃, hv₃, hle₃.trans hle₂⟩

/-- A step that keeps the bounds and the logged projections, does not restore `chk`, and does not
go back in the numbering. -/
private theorem of_le {s s' : State} (hn : s.next ≤ s'.next) (hd : s'.dbound = s.dbound)
    (hb : s'.bound = s.bound) (hc : s'.chk = true → s.chk = true) (hl : s'.logged = s.logged) :
    Mono F obj s s' :=
  ⟨hn, fun v hv => ⟨v, hd ▸ hv, le_rfl⟩, fun v hv => ⟨v, hb ▸ hv, le_rfl⟩, hc,
    hl ▸ List.suffix_refl _, fun _ => hl, fun _ _ hv => .inl (hb ▸ hv)⟩

end Mono

private theorem exists_mem_lowerTo {d : Option ℤ} {w : ℤ} (u : ℤ) (h : ∃ v ∈ d, v ≤ w) :
    ∃ v ∈ lowerTo d u, v ≤ w := by
  obtain ⟨v, hv, hw⟩ := h
  simp only [Option.mem_def] at hv
  subst hv
  exact ⟨_, rfl, (min_le_left _ _).trans hw⟩

/-- Logging a solution only lowers the bounds, and without `chk` lowers `bound` only to the input
objective value of a solution of `F`. -/
private theorem Mono.log {F : List PBConstr} {obj : Option Objective} {s : State}
    {ρ : List (Literal ℕ)} : Mono F obj s (s.log F obj ρ) := by
  refine ⟨le_rfl, fun v hv => exists_mem_lowerTo _ ⟨v, hv, le_rfl⟩, fun v hv => ?_, id,
    List.suffix_refl _, fun _ => rfl, fun hc v hv => ?_⟩
  · simp only [State.log]
    split
    · exact exists_mem_lowerTo _ ⟨v, hv, le_rfl⟩
    · split
      · exact exists_mem_lowerTo _ ⟨v, hv, le_rfl⟩
      · exact ⟨v, hv, le_rfl⟩
  · simp only [State.log, hc, Bool.false_eq_true, ↓reduceIte] at hv
    split at hv
    · rename_i hF
      rcases mem_lowerTo hv with rfl | hv
      · exact .inr ⟨_, holds_of_solves_normalize hF, rfl⟩
      · exact .inl hv
    · exact .inl hv

/-- Asserting an objective value only lowers `dbound`. -/
private theorem Mono.improve {F : List PBConstr} {obj : Option Objective} {s : State}
    {f : Objective} {v : ℤ} : Mono F obj s (s.improve f v) :=
  ⟨Nat.le_succ _, fun u hu => exists_mem_lowerTo _ ⟨u, hu, le_rfl⟩, fun u hu => ⟨u, hu, le_rfl⟩, id,
    List.suffix_refl _, fun _ => rfl, fun _ _ hu => .inl hu⟩

/-- **The monotonicity facts of a step** (`Cslib.Logic.PL.VeriPB.Mono`). -/
theorem stepTop_mono {F : List PBConstr} {obj : Option Objective} {s s' : State} {t : TopStep}
    (h : stepTop F obj s t = some s') : Mono F obj s s' := by
  cases t with
  | step st =>
    simp only [stepTop] at h
    split at h
    · rename_i db' n' hrun
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        refine .of_le (runStep_le _ _ _ _ _ hrun) rfl rfl (fun h => ?_) rfl
        simp only [Bool.and_eq_true] at h
        exact h.1
    · cases h
  | red c ω sub q =>
    simp only [stepTop] at h
    split at h
    · rename_i n' hred
      simp only [Option.some.injEq] at h
      subst h
      exact .of_le ((le_ite_of_le (redCheckP_le hred)).trans (Nat.le_succ _)) rfl rfl id rfl
    · cases h
  | sol ρ =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .log
    · cases h
  | soli ρ =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact Mono.log.trans .improve
      · cases h
    · cases h
  | deld ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .of_le le_rfl rfl rfl id rfl
    · cases h
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .of_le le_rfl rfl rfl (fun h => by cases h) rfl
    · cases h
  | delcChecked i ω sub q =>
    simp only [stepTop] at h
    split at h
    · split at h
      · split at h
        · rename_i n' hred
          simp only [Option.some.injEq] at h
          subst h
          exact .of_le (le_ite_of_le (redCheckP_le hred)) rfl rfl id rfl
        · cases h
      · cases h
    · cases h
  | core ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .of_le le_rfl rfl rfl id rfl
    · cases h
  | strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h <;>
      exact .of_le le_rfl rfl rfl id rfl
  | obji u =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .improve
    · cases h
  | obju diff g sub =>
    simp only [stepTop] at h
    split at h
    · split at h
      · rename_i n' hobj
        simp only [Option.some.injEq] at h
        subst h
        exact .of_le (objuCheck_le hobj) rfl rfl id rfl
      · cases h
    · cases h
  | solx ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i P _ _
      split at h
      · rename_i hok
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hok
        have h₁ : Mono F obj s ((s.log F obj ρ).addCore (exclusion P ρ)) :=
          Mono.log.trans (.of_le (Nat.le_succ _) rfl rfl id rfl)
        exact { h₁ with
          logged := List.suffix_cons _ _
          logged_eq := fun hc => by simp [hc] at hok }
      · cases h
    · cases h
  | defOrder name O sp w tp rp =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .of_le le_rfl rfl rfl id rfl
    · cases h
  | loadOrder name z =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact .of_le le_rfl rfl rfl id rfl
      · cases h
    · cases h
  | unloadOrder =>
    simp only [stepTop, Option.some.injEq] at h
    subst h
    exact .of_le le_rfl rfl rfl id rfl
  | presChange add x c sub =>
    simp only [stepTop] at h
    split at h
    · split at h
      · rename_i n' hchk
        simp only [Option.some.injEq] at h
        subst h
        exact .of_le (presChangeCheck_le hchk) rfl rfl id rfl
      · cases h
    · cases h
  | epreserved _ | eordDef _ _ | eordLoaded _ _ | econstr _ _ =>
    obtain ⟨-, ⟨⟩⟩ := Option.ite_none_right_eq_some.1 h
    exact .refl s
  | dom c ω sub q =>
    simp only [stepTop] at h
    split at h
    · split at h
      · rename_i n' hdom
        simp only [Option.some.injEq] at h
        subst h
        exact .of_le ((le_ite_of_le (domCheck_le hdom)).trans (Nat.le_succ _)) rfl rfl id rfl
      · cases h
    · cases h

/-- **The monotonicity facts of a run** (`Cslib.Logic.PL.VeriPB.Mono`), as CakePB's
`check_csteps_correct` states them. -/
theorem runTop_mono {F : List PBConstr} {obj : Option Objective} :
    ∀ {s : State} {ts : List TopStep} {s' : State}, runTop F obj s ts = some s' → Mono F obj s s'
  | s, [], s', h => by
    simp only [runTop, Option.some.injEq] at h
    exact h ▸ .refl s
  | s, t :: ts, s', h => by
    simp only [runTop] at h
    split at h
    · rename_i s₁ h₁
      exact (stepTop_mono h₁).trans (runTop_mono h)
    · cases h

/-! ### The order invariant -/

/-- **The order invariant** of a state: every defined order is good, and so is the loaded order,
if any, under which every solution of the core set gives a solution of the database below it in
the order, of no larger objective value, and with the same projection to the preserved set
(`Cslib.Logic.PL.VeriPB.SatObjPo`). This is the second conjunct of CakePB's `valid_conf`, which
CakePB asserts while no unchecked deletion has happened or an order is loaded. Here it is
asserted only while an order is loaded: without one, the forward step
(`Cslib.Logic.PL.VeriPB.stepTop_fwd`) needs no order, and the backward direction is in
`Cslib.Logic.PL.VeriPB.Inv.chk` and the counting injections. It justifies the goals of `dom`,
which cover only the core set. -/
structure OrdInv (s : State) : Prop where
  /-- Every defined order is good. -/
  orders : ∀ e ∈ s.orders, e.2.Good
  /-- The loaded order is good. -/
  loaded : ∀ L ∈ s.order, L.Good
  /-- CakePB's `sat_obj_po` from the core set to the database, under the loaded order. -/
  ord : ∀ L ∈ s.order, SatObjPo s.pres L s.obj s.core s.db

theorem ordInv_init (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) :
    OrdInv (State.init F obj pres) where
  orders _ h := by simp [State.init] at h
  loaded _ h := by simp [State.init] at h
  ord _ h := by simp [State.init] at h

/-- A step that keeps the orders and transports `sat_obj_po` keeps the order invariant. -/
private theorem OrdInv.of_ord {s s' : State} (ho : OrdInv s) (horders : s'.orders = s.orders)
    (horder : s'.order = s.order)
    (hord : ∀ L ∈ s.order, L.Good → SatObjPo s.pres L s.obj s.core s.db →
      SatObjPo s'.pres L s'.obj s'.core s'.db) : OrdInv s' where
  orders e he := ho.orders e (horders ▸ he)
  loaded L hL := ho.loaded L (horder ▸ hL)
  ord L hL := hord L (horder ▸ hL) (ho.loaded L (horder ▸ hL)) (ho.ord L (horder ▸ hL))

/-- Asserting a value of the objective keeps the order invariant: a solution of the database
below a solution of the core set has no larger value, so it satisfies the improving constraint
too. Shared by `soli` and `obji`. -/
private theorem ordInv_improve {s : State} {f : Objective} {v : ℤ} (ho : OrdInv s)
    (hf : s.obj = some f) : OrdInv (s.improve f v) :=
  ho.of_ord rfl rfl fun _ _ _ hsat τ hτ => by
    simp only [State.improve, State.addCore] at hτ ⊢
    have hi := hτ _ List.mem_cons_self
    obtain ⟨τ₁, h₁, hle₁, hobj₁, hp₁⟩ := hsat τ fun e he => hτ e (List.mem_cons_of_mem _ he)
    refine ⟨τ₁, List.forall_mem_cons.2 ⟨?_, h₁⟩, hle₁, hobj₁, hp₁⟩
    simp only [holds_normalize, Objective.holds_improving] at hi ⊢
    simp only [hf, objValue] at hobj₁
    omega

/-- **The repair of `dom`**: under the order invariant, every solution of the core set gives a
solution of the database and the new constraint below it (`Cslib.Logic.PL.VeriPB.SatObjPo.dom`),
shared by the order invariant and the forward step. -/
private theorem dom_repair {F : List PBConstr} {obj : Option Objective} {s : State}
    {L : LoadedOrder} {c : PBConstr} {ω : Witness} {items : List RedItem} {q : Option ℕ}
    {n' : ℕ} (m : ℕ) (hinv : Inv F obj s) (hord : OrdInv s) (hL : s.order = some L)
    (hdom : domCheck s.pres s.obj L s.db s.core s.next c ω items q = some n') :
    SatObjPo s.pres L s.obj s.core ((m, c.normalize) :: s.db) :=
  SatObjPo.dom m (hord.loaded L hL) (hord.ord L hL) (presFree_of_domCheck hdom) fun _ hσ hc =>
    domCheck_sound (hord.loaded L hL) hσ (allHold_mono hinv.sub hσ) hc hdom

/-- **Each step keeps the order invariant.** -/
theorem stepTop_ordInv {F : List PBConstr} {obj : Option Objective} {s s' : State} {t : TopStep}
    (hinv : Inv F obj s) (ho : OrdInv s) (h : stepTop F obj s t = some s') : OrdInv s' := by
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
        refine ho.of_ord rfl rfl fun L hL _ hsat τ hτ => ?_
        have hnt : (s.core.any fun e => st.delIds.contains e.1) = false := by
          simpa [Option.mem_def.1 hL] using htouch
        have hkeep : s.core.filter (fun e => !st.delIds.contains e.1) = s.core :=
          List.filter_eq_self.2 fun e he => by simpa using List.any_eq_false.1 hnt e he
        dsimp only at hτ ⊢
        rw [hkeep] at hτ
        obtain ⟨τ', h₁, h₂⟩ := hsat τ hτ
        exact ⟨τ', runStep_sound _ _ _ _ _ h₁ hrun, h₂⟩
    · cases h
  | red c ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i n' hred
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hfree, hred⟩ := redCheckOn_of_redCheckP hred
      refine ho.of_ord rfl rfl fun L hL hLg hsat τ hτ => ?_
      simp only [State.addStrengthened] at hτ ⊢
      generalize (if items.isSome = true then n' else s.next) = m at hτ ⊢
      cases ht : s.tcb
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hτ hred
        obtain ⟨τ₁, h₁, hle₁, hobj₁, hp₁⟩ := hsat τ hτ
        obtain ⟨τ₂, hτ₂, h₂, hobj₂, hle₂⟩ := redCheckOn_sound ho.loaded h₁ h₁ hred
        refine ⟨τ₂, List.forall_mem_cons.2 ⟨(h₂ _ List.mem_cons_self : c.normalize.Holds τ₂),
          fun e he => h₂ e (List.mem_cons_of_mem _ he)⟩, hLg.le_trans (hle₂ L hL) hle₁,
          hobj₂.trans hobj₁, fun P hP => Eq.trans ?_ (hp₁ P hP)⟩
        rcases hτ₂ with rfl | rfl
        · rfl
        · exact proj_apply_of_presFree hfree τ₁ P hP
      · simp only [ht, ↓reduceIte] at hτ
        exact SatObjPo.refl hLg (fun τ hτ => List.forall_mem_cons.2 ⟨hτ _ List.mem_cons_self,
          hinv.imp ht τ fun e he => hτ e (List.mem_cons_of_mem _ he)⟩) τ hτ
    · cases h
  | sol ρ =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ho.of_ord rfl rfl fun _ _ _ hsat => hsat
    · cases h
  | soli ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ordInv_improve (ho.of_ord rfl rfl fun _ _ _ hsat => hsat) hf
      · cases h
    · cases h
  | deld ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      refine ho.of_ord rfl rfl fun L hL _ hsat τ hτ => ?_
      obtain ⟨τ₁, h₁, h₂⟩ := hsat τ hτ
      exact ⟨τ₁, allHold_filter h₁ _, h₂⟩
    · cases h
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
      refine ho.of_ord rfl rfl fun L hL hLg _ => SatObjPo.refl hLg fun τ hτ e he => ?_
      rw [List.mem_filter] at he
      rcases hok.2 with hf | hd
      · rw [Option.mem_def.1 hL] at hf; simp at hf
      · exact hτ e (List.mem_filter.2
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
          refine ho.of_ord rfl rfl fun L hL hLg hsat τ hτ => ?_
          obtain ⟨hfree, hred⟩ := redCheckOn_of_redCheckP hred
          obtain ⟨τ', hτ', hall, hobj', hle'⟩ := redCheckOn_sound ho.loaded hτ hτ hred
          obtain ⟨τ₁, h₁, hle₁, hobj₁, hp₁⟩ := hsat τ' (allHold_core_of_filter (hinv.core_all hc)
            (fun e he => hall e (List.mem_cons_of_mem _ he))
            ((holds_normalize _ _).1 (hall _ List.mem_cons_self)))
          refine ⟨τ₁, allHold_filter h₁ _, hLg.le_trans hle₁ (hle' L hL), hobj₁.trans hobj',
            fun P hP => (hp₁ P hP).trans ?_⟩
          rcases hτ' with rfl | rfl
          · rfl
          · exact proj_apply_of_presFree hfree τ P hP
        · cases h
      · cases h
    · cases h
  | core ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ho.of_ord rfl rfl fun _ _ _ hsat τ hτ =>
        hsat τ fun e he => hτ e (List.mem_append_right _ he)
    · cases h
  | strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h
    · exact ho.of_ord rfl rfl fun _ _ _ hsat => hsat
    · exact ho.of_ord rfl rfl fun _ _ hLg _ => SatObjPo.refl hLg fun _ hτ => hτ
  | obji u =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      simp only [Option.some.injEq] at h
      subst h
      exact ordInv_improve ho hf
    · cases h
  | obju diff g sub =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · rename_i n' hobj
        simp only [Option.some.injEq] at h
        subst h
        refine ho.of_ord rfl rfl fun L hL _ hsat τ hτ => ?_
        obtain ⟨τ₁, h₁, hle₁, hobj₁, hp₁⟩ := hsat τ hτ
        refine ⟨τ₁, h₁, hle₁, ?_, hp₁⟩
        simp only [hf, objValue] at hobj₁ ⊢
        rw [objuCheck_sound hτ hobj, objuCheck_sound (allHold_mono hinv.sub h₁) hobj]
        exact hobj₁
      · cases h
    · cases h
  | solx ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i P hP hobj
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        refine ho.of_ord rfl rfl fun L hL _ hsat τ hτ => ?_
        simp only [State.log] at hτ ⊢
        have hex := hτ _ List.mem_cons_self
        obtain ⟨τ₁, h₁, hle₁, hobj₁, hp₁⟩ := hsat τ fun e he => hτ e (List.mem_cons_of_mem _ he)
        refine ⟨τ₁, List.forall_mem_cons.2 ⟨?_, h₁⟩, hle₁, hobj₁, hp₁⟩
        have hp := hp₁ P (by rw [hP]; rfl)
        simp only [holds_exclusion] at hex ⊢
        rwa [hp]
      · cases h
    · cases h
  | defOrder name O w tp rp =>
    simp only [stepTop] at h
    split at h
    · rename_i hchk
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨fun e he => ?_, ho.loaded, ho.ord⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact Order.good_of_defCheck hchk
      · exact ho.orders e he
    · cases h
  | loadOrder name z =>
    simp only [stepTop] at h
    split at h
    · rename_i O hO
      split at h
      · rename_i hz
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hz
        have hL : LoadedOrder.Good ⟨O, z⟩ :=
          ⟨ho.orders (name, O) (by
            obtain ⟨l₁, l₂, he, -⟩ := List.lookup_eq_some_iff.1 hO
            simp [he]), hz.1, fun l hl => by simpa using hz.2 l hl⟩
        refine ⟨ho.orders, fun L hL' => ?_, fun L hL' => ?_⟩ <;>
          simp only [Option.mem_def, Option.some.injEq] at hL' <;> subst hL'
        · exact hL
        · exact SatObjPo.refl hL fun _ hτ => hτ
      · cases h
    · cases h
  | unloadOrder =>
    simp only [stepTop, Option.some.injEq] at h
    subst h
    exact ⟨ho.orders, fun _ h => by simp at h, fun _ h => by simp at h⟩
  | presChange add x c sub =>
    simp only [stepTop] at h
    split at h
    · rename_i P hP
      split at h
      · rename_i n' hchk
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hvars, hiff⟩ := presChangeCheck_sound hchk
        refine ho.of_ord rfl rfl fun L _ _ hsat τ hτ => ?_
        obtain ⟨τ', h₁, hle, hobj, hp⟩ := hsat τ hτ
        refine ⟨τ', h₁, hle, hobj, fun P' hP' => ?_⟩
        simp only [Option.mem_def, Option.some.injEq] at hP'
        subst hP'
        have hag : ∀ v ∈ P, τ' v = τ v := proj_eq_iff.1 (hp P (by simp [hP]))
        rw [proj_eq_iff]
        cases add
        · intro v hv
          exact hag v (List.mem_filter.1 hv).1
        · intro v hv
          rcases List.mem_insert_iff.1 hv with rfl | hv
          · have hc : c.Holds τ' ↔ c.Holds τ := by
              rw [← holds_normalize, ← holds_normalize _ c]
              exact holds_congr fun t ht => hag _ (hvars t ht).1
            rw [Bool.eq_iff_iff, hiff τ' (allHold_mono hinv.sub h₁), hiff τ hτ, hc]
          · exact hag v hv
      · cases h
    · cases h
  | epreserved _ | eordDef _ _ | eordLoaded _ _ | econstr _ _ =>
    obtain ⟨-, ⟨⟩⟩ := Option.ite_none_right_eq_some.1 h
    exact ho
  | dom c ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i L hL
      split at h
      · rename_i n' hdom
        simp only [Option.some.injEq] at h
        subst h
        refine ho.of_ord rfl rfl fun L' hL' _ _ τ hτ => ?_
        rw [hL, Option.mem_def, Option.some.injEq] at hL'
        subst hL'
        refine dom_repair _ hinv ho hL hdom τ ?_
        simp only [State.addStrengthened] at hτ
        split at hτ
        · exact fun e he => hτ e (List.mem_cons_of_mem _ he)
        · exact hτ
      · cases h
    · cases h

/-- **The lower-bound invariant** for a value `w`: some solution of the database has objective at
most `w`, or the bound `dbound` is at most `w`. It is CakePB's `bimp_obj`, the existence half of
the forward counting injection (`Cslib.Logic.PL.VeriPB.InjInv.reaches`). -/
@[expose]
def Reaches (w : ℤ) (s : State) : Prop :=
  (∃ τ, AllHold τ s.db ∧ objValue s.obj τ ≤ w) ∨ ∃ d ∈ s.dbound, d ≤ w


private theorem lowerTo_le (d : Option ℤ) (u : ℤ) : ∃ v ∈ lowerTo d u, v ≤ u := by
  cases d
  · exact ⟨u, rfl, le_rfl⟩
  · exact ⟨_, rfl, min_le_right _ _⟩

/-- A solution of the database survives a checked `red` step: the repaired valuation, `τ` itself
or `τ ∘ ω`, satisfies the new constraint and the whole database, in strengthening-to-core mode by
the core invariant, without a larger objective value. -/
private theorem red_repair {F : List PBConstr} {obj : Option Objective} {s : State}
    {c : PBConstr} {ω : Witness} {items : List RedItem} {q : Option ℕ} {n₁ : ℕ} (m : ℕ)
    {τ : ℕ → Bool} (hinv : Inv F obj s) (hord : ∀ L ∈ s.order, L.Good) (hτ : AllHold τ s.db)
    (h₁ : redCheckOn s.obj s.order s.db (if s.tcb then s.core else s.db) s.next c ω items q =
      some n₁) :
    ∃ τ', (τ' = τ ∨ τ' = Witness.apply τ ω) ∧ AllHold τ' ((m, c.normalize) :: s.db) ∧
      objValue s.obj τ' ≤ objValue s.obj τ := by
  have hgs : AllHold τ (if s.tcb then s.core else s.db) := by
    split
    · exact allHold_mono hinv.sub hτ
    · exact hτ
  obtain ⟨τ', hτ'eq, hτ', hle, -⟩ := redCheckOn_sound hord hτ hgs h₁
  refine ⟨τ', hτ'eq, List.forall_mem_cons.2
    ⟨(hτ' (n₁, c.normalize) List.mem_cons_self : c.normalize.Holds τ'), ?_⟩, hle⟩
  have hτ'' := fun e he => hτ' e (List.mem_cons_of_mem _ he)
  split at hτ''
  · rename_i ht
    exact hinv.imp ht τ' hτ''
  · exact hτ''

/-- Asserting the value `u` of the current objective `f` keeps a solution of the database below
`u`, with the improving constraint, and otherwise `u`, the new bound `dbound`, is at most its
value. Shared by `soli` and `obji`. -/
private theorem fwd_improve {f : Objective} {u : ℤ} {s : State} (hf : s.obj = some f)
    {τ : ℕ → Bool} (hτ : AllHold τ s.db) :
    (∃ τ', AllHold τ' (s.improve f u).db ∧ objValue s.obj τ' ≤ objValue s.obj τ ∧
      ∀ P ∈ s.pres, proj P τ' = proj P τ) ∨ ∃ d ∈ (s.improve f u).dbound, d ≤ objValue s.obj τ := by
  by_cases hlt : f.eval τ < u
  · refine .inl ⟨τ, List.forall_mem_cons.2 ⟨?_, hτ⟩, le_rfl, fun _ _ => rfl⟩
    exact (holds_normalize _ _).2 ((Objective.holds_improving _ _ _).2 hlt)
  · obtain ⟨v, hv, hle⟩ := lowerTo_le s.dbound u
    refine .inr ⟨v, hv, ?_⟩
    simp only [hf, objValue]
    omega

/-- **A step keeps or cuts off each solution of the database**, the forward half of CakePB's
`check_cstep_correct`: a solution `τ` of the database before the step gives one after it, of no
larger objective value and with the same projection to the preserved set; or the new bound
`dbound` is at most the value of `τ`, and then, without an objective, the step is `solx` and has
logged the projection of `τ`. The order invariant is needed for `dom`, whose repaired solution
agrees with `τ` only on the preserved set. -/
theorem stepTop_fwd {F : List PBConstr} {obj : Option Objective} {s s' : State} {t : TopStep}
    (hinv : Inv F obj s) (hord : OrdInv s) (h : stepTop F obj s t = some s') {τ : ℕ → Bool}
    (hτ : AllHold τ s.db) :
    (∃ τ', AllHold τ' s'.db ∧ objValue s'.obj τ' ≤ objValue s.obj τ ∧
      ∀ P ∈ s.pres, proj P τ' = proj P τ) ∨
    (∃ d ∈ s'.dbound, d ≤ objValue s.obj τ) ∧
      (s.obj = none → ∃ P ∈ s.pres, s'.logged = proj P τ :: s.logged) := by
  cases t with
  | step st =>
    simp only [stepTop] at h
    split at h
    · rename_i db₁ n₁ h₁
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        exact .inl ⟨τ, runStep_sound _ _ _ _ _ hτ h₁, le_rfl, fun _ _ => rfl⟩
    · cases h
  | red c ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i n₁ h₁
      simp only [Option.some.injEq] at h
      subst h
      generalize (if items.isSome = true then n₁ else s.next) = m
      obtain ⟨hfree, h₁⟩ := redCheckOn_of_redCheckP h₁
      obtain ⟨τ', hτ'eq, hτ', hle⟩ := red_repair m hinv hord.loaded hτ h₁
      refine .inl ⟨τ', hτ', hle, fun P hP => ?_⟩
      rcases hτ'eq with rfl | rfl
      · rfl
      · exact proj_apply_of_presFree hfree τ P hP
    · cases h
  | sol ρ =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl ⟨τ, hτ, le_rfl, fun _ _ => rfl⟩
    · cases h
  | soli ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rcases fwd_improve (s := s.log F obj ρ) (u := f.eval (assignOf ρ)) hf hτ with h' | h'
        · exact .inl h'
        · exact .inr ⟨h', fun h0 => by simp [hf] at h0⟩
      · cases h
    · cases h
  | deld ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl ⟨τ, allHold_filter hτ _, le_rfl, fun _ _ => rfl⟩
    · cases h
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl ⟨τ, allHold_filter hτ _, le_rfl, fun _ _ => rfl⟩
    · cases h
  | delcChecked i ω items q =>
    simp only [stepTop] at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact .inl ⟨τ, allHold_filter hτ _, le_rfl, fun _ _ => rfl⟩
        · cases h
      · cases h
    · cases h
  | core ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl ⟨τ, hτ, le_rfl, fun _ _ => rfl⟩
    · cases h
  | strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h <;>
      exact .inl ⟨τ, hτ, le_rfl, fun _ _ => rfl⟩
  | obji u =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      simp only [Option.some.injEq] at h
      subst h
      rcases fwd_improve (u := u) hf hτ with h' | h'
      · exact .inl h'
      · exact .inr ⟨h', fun h0 => by simp [hf] at h0⟩
    · cases h
  | obju diff g sub =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · rename_i n' hobj
        simp only [Option.some.injEq] at h
        subst h
        refine .inl ⟨τ, hτ, ?_, fun _ _ => rfl⟩
        simp only [objValue, hf]
        rw [objuCheck_sound (allHold_mono hinv.sub hτ) hobj]
      · cases h
    · cases h
  | solx ρ =>
    simp only [stepTop] at h
    split at h
    · rename_i Q hQ hobj
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        by_cases hex : (exclusion Q ρ).Holds τ
        · exact .inl ⟨τ, List.forall_mem_cons.2 ⟨hex, hτ⟩, le_rfl, fun _ _ => rfl⟩
        · obtain ⟨v, hv, hle⟩ := lowerTo_le s.dbound (objValue s.obj (assignOf ρ))
          rw [holds_exclusion, not_not] at hex
          refine .inr ⟨⟨v, hv, ?_⟩, fun _ => ⟨Q, hQ, ?_⟩⟩
          · simp only [hobj, objValue] at hle ⊢
            exact hle
          · simp only [hex]
      · cases h
    · cases h
  | defOrder name O w tp rp =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl ⟨τ, hτ, le_rfl, fun _ _ => rfl⟩
    · cases h
  | loadOrder name z =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact .inl ⟨τ, hτ, le_rfl, fun _ _ => rfl⟩
      · cases h
    · cases h
  | unloadOrder =>
    simp only [stepTop, Option.some.injEq] at h
    subst h
    exact .inl ⟨τ, hτ, le_rfl, fun _ _ => rfl⟩
  | presChange add x c sub =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact .inl ⟨τ, hτ, le_rfl, fun _ _ => rfl⟩
      · cases h
    · cases h
  | epreserved _ | eordDef _ _ | eordLoaded _ _ | econstr _ _ =>
    obtain ⟨-, ⟨⟩⟩ := Option.ite_none_right_eq_some.1 h
    exact .inl ⟨τ, hτ, le_rfl, fun _ _ => rfl⟩
  | dom c ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i L hL
      split at h
      · rename_i n' hdom
        simp only [Option.some.injEq] at h
        subst h
        have hd := dom_repair (if items.isSome = true then n' else s.next) hinv hord hL hdom
        obtain ⟨τ', h', -, hle, hp'⟩ := hd τ (allHold_mono hinv.sub hτ)
        exact .inl ⟨τ', h', hle, hp'⟩
      · cases h
    · cases h

/-- **A step gives back each solution of the core set**, the backward half of CakePB's
`check_cstep_correct`: while no unchecked deletion has happened, a solution of the core set after
the step comes from one before it, of no larger objective value and with the same projection to
the preserved set. A checked deletion repairs it with a witness that leaves the preserved set
alone. -/
theorem stepTop_back {F : List PBConstr} {obj : Option Objective} {s s' : State} {t : TopStep}
    (hinv : Inv F obj s) (hord : ∀ L ∈ s.order, L.Good) (h : stepTop F obj s t = some s')
    (hc : s'.chk = true) {τ : ℕ → Bool} (hτ : AllHold τ s'.core) :
    s.chk = true ∧ ∃ τ₀, AllHold τ₀ s.core ∧ objValue s.obj τ₀ ≤ objValue s'.obj τ ∧
      ∀ P ∈ s.pres, proj P τ₀ = proj P τ := by
  have cons : ∀ e (τ : ℕ → Bool), AllHold τ (e :: s.core) → AllHold τ s.core :=
    fun _ _ hτ e he => hτ e (List.mem_cons_of_mem _ he)
  cases t with
  | step st =>
    simp only [stepTop] at h
    split at h
    · split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        have hkeep : s.core.filter (fun e => !st.delIds.contains e.1) = s.core :=
          List.filter_eq_self.2 fun e he => by
            have := List.any_eq_false.1 hc.2 e he
            simpa using this
        refine ⟨hc.1, τ, ?_, le_rfl, fun _ _ => rfl⟩
        rw [← hkeep]
        exact hτ
    · cases h
  | red c ω items q | dom c ω items q =>
    simp only [stepTop] at h
    repeat' split at h
    all_goals first
      | cases h; done
      | simp only [Option.some.injEq] at h
        subst h
        refine ⟨hc, τ, ?_, le_rfl, fun _ _ => rfl⟩
        simp only [State.addStrengthened] at hτ
        split at hτ
        · exact cons _ τ hτ
        · exact hτ
  | sol ρ | deld _ | defOrder _ _ _ _ _ | unloadOrder | presChange _ _ _ _ =>
    simp only [stepTop] at h
    repeat' split at h
    all_goals first
      | cases h; done
      | simp only [Option.some.injEq] at h
        subst h
        exact ⟨hc, τ, hτ, le_rfl, fun _ _ => rfl⟩
  | soli ρ | obji _ =>
    simp only [stepTop] at h
    repeat' split at h
    all_goals first
      | cases h; done
      | simp only [Option.some.injEq] at h
        subst h
        exact ⟨hc, τ, cons _ τ hτ, le_rfl, fun _ _ => rfl⟩
  | delc ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      cases hc
    · cases h
  | delcChecked i ω items q =>
    simp only [stepTop] at h
    split at h
    · rename_i c hc'
      split at h
      · split at h
        · rename_i n' hred
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hfree, hred⟩ := redCheckOn_of_redCheckP hred
          obtain ⟨τ', hτ', hall, hle, -⟩ := redCheckOn_sound hord hτ hτ hred
          refine ⟨hc, τ', allHold_core_of_filter (hinv.core_all hc') (fun e he => hall e
            (List.mem_cons_of_mem _ he)) ((holds_normalize _ _).1 (hall _ List.mem_cons_self)),
            hle, fun P hP => ?_⟩
          rcases hτ' with rfl | rfl
          · rfl
          · exact proj_apply_of_presFree hfree τ P hP
        · cases h
      · cases h
    · cases h
  | core ids =>
    simp only [stepTop] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨hc, τ, fun e he => hτ e (List.mem_append_right _ he), le_rfl, fun _ _ => rfl⟩
    · cases h
  | strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h
    · exact ⟨hc, τ, hτ, le_rfl, fun _ _ => rfl⟩
    · exact ⟨hc, τ, allHold_mono hinv.sub hτ, le_rfl, fun _ _ => rfl⟩
  | obju diff g sub =>
    simp only [stepTop] at h
    split at h
    · rename_i f hf
      split at h
      · rename_i n' hobj
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨hc, τ, hτ, ?_, fun _ _ => rfl⟩
        simp only [objValue, hf]
        rw [objuCheck_sound hτ hobj]
      · cases h
    · cases h
  | solx ρ =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨hc, τ, cons _ τ hτ, le_rfl, fun _ _ => rfl⟩
      · cases h
    · cases h
  | loadOrder name z =>
    simp only [stepTop] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨hc, τ, allHold_mono hinv.sub hτ, le_rfl, fun _ _ => rfl⟩
      · cases h
    · cases h
  | epreserved _ | eordDef _ _ | eordLoaded _ _ | econstr _ _ =>
    obtain ⟨-, ⟨⟩⟩ := Option.ite_none_right_eq_some.1 h
    exact ⟨hc, τ, hτ, le_rfl, fun _ _ => rfl⟩

/-- What a step leaves alone, beyond the monotonicity facts (`Cslib.Logic.PL.VeriPB.Mono`): a
missing objective stays missing, only `solx` logs, and only `preserved_add` and `preserved_rm`
change the preserved set. -/
private theorem stepTop_frame {F : List PBConstr} {obj : Option Objective} {s s' : State}
    {t : TopStep} (h : stepTop F obj s t = some s') :
    (s.obj = none → s'.obj = none) ∧ ((∃ ρ, t = .solx ρ) ∨ s'.logged = s.logged) ∧
      ((∃ add x c sub, t = .presChange add x c sub) ∨
        s'.pres = s.pres ∧ s'.presChanged = s.presChanged) := by
  cases t
  case solx ρ =>
    simp only [stepTop] at h
    repeat' split at h
    all_goals first
      | cases h; done
      | simp only [Option.some.injEq] at h
        subst h
        exact ⟨id, .inl ⟨ρ, rfl⟩, .inr ⟨rfl, rfl⟩⟩
  case presChange add x c sub =>
    simp only [stepTop] at h
    repeat' split at h
    all_goals first
      | cases h; done
      | simp only [Option.some.injEq] at h
        subst h
        exact ⟨id, .inr rfl, .inl ⟨add, x, c, sub, rfl⟩⟩
  case obju diff g sub =>
    simp only [stepTop] at h
    repeat' split at h
    all_goals first
      | cases h; done
      | simp only [Option.some.injEq] at h
        subst h
        exact ⟨fun h0 => by simp_all, .inr rfl, .inr ⟨rfl, rfl⟩⟩
  case strengthenToCore b =>
    unfold stepTop at h
    cases b <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h <;> subst h <;>
      exact ⟨id, .inr rfl, .inr ⟨rfl, rfl⟩⟩
  all_goals
    simp only [stepTop] at h
    repeat' split at h
    all_goals first
      | cases h; done
      | simp only [Option.some.injEq] at h
        subst h
        exact ⟨id, .inr rfl, .inr ⟨rfl, rfl⟩⟩

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

/-! ### The counting injections -/

/-- The solutions of the formula `F` of value at most `v` under the objective `obj`. -/
@[expose]
def solsLE (F : List PBConstr) (obj : Option Objective) (v : ℤ) : Set (ℕ → Bool) :=
  {σ | (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ v}

/-- **The forward target** of the state `s` for the bound `v`: the projections to the preserved
set of the solutions of the database of value at most `v`, and the indices of the logged
projections, counted from the first, once `dbound` is at most `v`. -/
@[expose]
def State.fwdTarget (s : State) (v : ℤ) : Set (List Bool ⊕ ℕ) :=
  Sum.inl '' (proj (s.pres.getD []) '' {τ | AllHold τ s.db ∧ objValue s.obj τ ≤ v}) ∪
    Sum.inr '' {k | k < s.logged.length ∧ ∃ d ∈ s.dbound, d ≤ v}

/-- **The backward source** of the state `s` for the bound `v`: while no unchecked deletion has
happened, the projections to the preserved set of the solutions of the core set of value at most
`v`; and the indices of the logged projections, of value `0` (they are logged without an
objective), if `0 ≤ v`. -/
@[expose]
def State.bwdSource (s : State) (v : ℤ) : Set (List Bool ⊕ ℕ) :=
  Sum.inl '' (proj (s.pres.getD []) ''
      {τ | s.chk = true ∧ AllHold τ s.core ∧ objValue s.obj τ ≤ v}) ∪
    Sum.inr '' {k | k < s.logged.length ∧ 0 ≤ v}

/-- **The counting injections** of a state for the formula `F`, the input objective `obj` and the
preserved set `pres`: CakePB's `bimp_pres_obj`, with the logged projections of its `bimp_pres`
(`check_cstep_correct`, `npbc_checkScript.sml`, CakeML commit `14856fcf`). For each bound `v`:
* forward, below `dbound` or without an objective, an injection from the projections to `pres` of
  the solutions of `F` of value at most `v` into the forward target
  (`Cslib.Logic.PL.VeriPB.State.fwdTarget`): the projections to the current preserved set of the
  solutions of the database of value at most `v`, and the logged projections;
* backward, an injection from the backward source (`Cslib.Logic.PL.VeriPB.State.bwdSource`), the
  projections of the solutions of the core set while no unchecked deletion has happened, and the
  logged projections, into the projections of the solutions of `F` of value at most `v`.

While the preserved set is unchanged, it is `pres`, and both injections are the identity on the
projections of solutions. A change of the preserved set maps projections to the old set to
projections to the new one, as `x ⇔ C` on the core set, with `C` over the variables kept. The
logged projections are counted by their indices, so that the counts are the length of the log.

The backward injection holds for every `v`, not only below `bound` as in CakePB, and without
`chk` it still bounds the number of logged projections. -/
structure InjInv (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ))
    (s : State) : Prop where
  /-- While unchanged, the preserved set is `pres`. -/
  pres_eq : s.presChanged = false → s.pres = pres
  /-- There is a preserved set exactly when `pres` is one. -/
  pres_some : s.pres.isSome = pres.isSome
  /-- Without an input objective there is no current one. -/
  obj_none : obj = none → s.obj = none
  /-- The forward injection. -/
  fwd : ∀ v, ((∀ d ∈ s.dbound, v < d) ∨ obj = none) →
    ∃ f : List Bool → List Bool ⊕ ℕ, Set.InjOn f (proj (pres.getD []) '' solsLE F obj v) ∧
      Set.MapsTo f (proj (pres.getD []) '' solsLE F obj v) (s.fwdTarget v) ∧
      (s.presChanged = false →
        ∀ l ∈ proj (pres.getD []) '' solsLE F obj v, ∀ m, f l = .inl m → m = l)
  /-- The backward injection. -/
  bwd : ∀ v, ∃ g : List Bool ⊕ ℕ → List Bool, Set.InjOn g (s.bwdSource v) ∧
    Set.MapsTo g (s.bwdSource v) (proj (pres.getD []) '' solsLE F obj v) ∧
    (s.presChanged = false → ∀ m, .inl m ∈ s.bwdSource v → g (.inl m) = m)

theorem injInv_init (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) :
    InjInv F obj pres (State.init F obj pres) where
  pres_eq _ := rfl
  pres_some := rfl
  obj_none h := h
  fwd v _ := by
    refine ⟨Sum.inl, Sum.inl_injective.injOn, ?_, fun _ _ _ _ h => (Sum.inl_injective h).symm⟩
    rintro _ ⟨σ, ⟨hσ, hv⟩, rfl⟩
    exact .inl ⟨_, ⟨σ, ⟨allHold_initDb hσ, hv⟩, rfl⟩, rfl⟩
  bwd v := by
    refine ⟨Sum.elim id fun _ => [], ?_, ?_, fun _ _ _ => rfl⟩
    · rintro (a | a) (⟨_, -, ⟨⟩⟩ | ⟨k, ⟨hk, -⟩, -⟩) (b | b) (⟨_, -, ⟨⟩⟩ | ⟨k', ⟨hk', -⟩, -⟩) hab <;>
        simp_all [State.init]
    · rintro _ (⟨_, ⟨τ, ⟨-, hτ, hv⟩, rfl⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, -⟩)
      · exact ⟨τ, ⟨holds_of_allHold_initDb hτ, hv⟩, rfl⟩
      · simp [State.init] at hk

/-- The projection to the preserved set of a state, as a list: the preserved set if there is one,
and no variable otherwise. -/
private theorem proj_getD {pres : Option (List ℕ)} {σ τ : ℕ → Bool}
    (h : ∀ P ∈ pres, proj P σ = proj P τ) : proj (pres.getD []) σ = proj (pres.getD []) τ := by
  cases pres with
  | none => rfl
  | some P => exact h P rfl

/-- If the projections to `P` determine those to `Q` on `A`, some map on lists carries the one to
the other. -/
private theorem exists_proj_map {A : Set (ℕ → Bool)} {P Q : List ℕ}
    (h : ∀ a ∈ A, ∀ b ∈ A, proj P a = proj P b → proj Q a = proj Q b) :
    ∃ φ : List Bool → List Bool, ∀ a ∈ A, φ (proj P a) = proj Q a := by
  classical
  refine ⟨fun l => if hl : ∃ a ∈ A, proj P a = l then proj Q hl.choose else l, fun a ha => ?_⟩
  dsimp only
  split
  · rename_i hl
    exact h _ hl.choose_spec.1 a ha hl.choose_spec.2
  · rename_i hl
    exact absurd ⟨a, ha, rfl⟩ hl

/-- **Projections that determine each other** are in bijection: if, on `A`, the projections to
`P` and to `Q` determine each other, some map carries the projections to `P` of `A` injectively
onto those to `Q`. -/
theorem exists_proj_injOn {A : Set (ℕ → Bool)} {P Q : List ℕ}
    (h : ∀ a ∈ A, ∀ b ∈ A, proj P a = proj P b ↔ proj Q a = proj Q b) :
    ∃ φ : List Bool → List Bool, Set.InjOn φ (proj P '' A) ∧
      Set.MapsTo φ (proj P '' A) (proj Q '' A) ∧ ∀ a ∈ A, φ (proj P a) = proj Q a := by
  obtain ⟨φ, hφ⟩ := exists_proj_map fun a ha b hb => (h a ha b hb).1
  refine ⟨φ, ?_, ?_, hφ⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hφ a ha, hφ b hb] at hab
    exact (h a ha b hb).2 hab
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (hφ a ha).symm⟩

/-- **A change of the preserved set keeps the projections in correspondence**: if
`preserved_add x : C` or `preserved_rm x : C` checks against the core set, then on the solutions
of the core set the projections to the old and to the new preserved set determine each other,
since `x ⇔ C` there and `C` mentions only variables of both. -/
theorem proj_eq_iff_of_presChangeCheck {core : List (ℕ × PBConstr)} {n n' : ℕ} {P : List ℕ}
    {x : ℕ} {c : PBConstr} {items : List RedItem}
    (hchk : presChangeCheck core n P x c items = some n')
    (add : Bool) {a b : ℕ → Bool} (ha : AllHold a core) (hb : AllHold b core) :
    proj P a = proj P b ↔
      proj (if add then P.insert x else P.filter (· != x)) a =
        proj (if add then P.insert x else P.filter (· != x)) b := by
  obtain ⟨hvars, hiff⟩ := presChangeCheck_sound hchk
  have hx : (∀ v ∈ P, v ≠ x → a v = b v) → a x = b x := fun hag => by
    have hC : c.Holds a ↔ c.Holds b := by
      rw [← holds_normalize, ← holds_normalize b]
      exact holds_congr fun t ht => hag _ (hvars t ht).1 (hvars t ht).2
    exact Bool.eq_iff_iff.2 ((hiff a ha).trans (hC.trans (hiff b hb).symm))
  simp only [proj_eq_iff]
  cases add
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_filter, bne_iff_ne, ne_eq,
      and_imp]
    refine ⟨fun h v hv _ => h v hv, fun h v hv => ?_⟩
    by_cases hvx : v = x
    · exact hvx ▸ hx fun w hw hwx => h w hw hwx
    · exact h v hv hvx
  · simp only [↓reduceIte, List.mem_insert_iff, forall_eq_or_imp]
    exact ⟨fun h => ⟨hx fun v hv _ => h v hv, h⟩, fun h => h.2⟩

/-- A step that changes neither the log nor the preserved set keeps the counting injections:
the forward target only grows and the backward source only shrinks. -/
private theorem injInv_of_frame {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {s s' : State} (he : InjInv F obj pres s)
    (hdb : ∀ d ∈ s.dbound, ∃ d' ∈ s'.dbound, d' ≤ d) (hobj : s.obj = none → s'.obj = none)
    (hpres : s'.pres = s.pres) (hpc : s'.presChanged = s.presChanged)
    (hfwd : ∀ v, ((∀ d ∈ s'.dbound, v < d) ∨ obj = none) → s.fwdTarget v ⊆ s'.fwdTarget v)
    (hbwd : ∀ v, s'.bwdSource v ⊆ s.bwdSource v) : InjInv F obj pres s' where
  pres_eq h := hpres.trans (he.pres_eq (hpc ▸ h))
  pres_some := hpres ▸ he.pres_some
  obj_none h := hobj (he.obj_none h)
  fwd v hv := by
    have hv' : (∀ d ∈ s.dbound, v < d) ∨ obj = none := by
      rcases hv with hv | hv
      · refine .inl fun d hd => ?_
        obtain ⟨d', hd', hle⟩ := hdb d hd
        exact (hv d' hd').trans_le hle
      · exact .inr hv
    obtain ⟨f, hinj, hmaps, hid⟩ := he.fwd v hv'
    exact ⟨f, hinj, hmaps.mono_right (hfwd v hv), fun h => hid (hpc ▸ h)⟩
  bwd v := by
    obtain ⟨g, hinj, hmaps, hid⟩ := he.bwd v
    exact ⟨g, hinj.mono (hbwd v), hmaps.mono_left (hbwd v),
      fun h m hm => hid (hpc ▸ h) m (hbwd v hm)⟩

/-- **Each step keeps the counting injections**, CakePB's `bimp_pres_obj` part of
`check_csteps_correct`. A step other than `solx` and the changes of the preserved set keeps or
cuts off each solution of the database (`Cslib.Logic.PL.VeriPB.stepTop_fwd`) and gives back each
solution of the core set (`Cslib.Logic.PL.VeriPB.stepTop_back`), with the same projection; a cut
needs `dbound` at most the value, hence above the bound or an objective, and `dbound` only
decreases (`Cslib.Logic.PL.VeriPB.stepTop_mono`). `solx` cuts off exactly
the projection it logs, which takes the next index. A change of the preserved set composes the
injections with the bijection between the old and the new projections
(`Cslib.Logic.PL.VeriPB.proj_eq_iff_of_presChangeCheck`). -/
theorem stepTop_injInv {F : List PBConstr} {obj : Option Objective} {pres : Option (List ℕ)}
    {s s' : State} {t : TopStep} (hinv : Inv F obj s) (hord : OrdInv s)
    (he : InjInv F obj pres s) (h : stepTop F obj s t = some s') : InjInv F obj pres s' := by
  have hdb := (stepTop_mono h).dbound
  obtain ⟨hobj, hlog, hpres⟩ := stepTop_frame h
  rcases hpres with ⟨add, x, c, sub, rfl⟩ | ⟨hpres, hpc⟩
  · -- A change of the preserved set: compose with the bijection of projections.
    simp only [stepTop] at h
    split at h
    · rename_i P hP
      split at h
      · rename_i n' hchk
        simp only [Option.some.injEq] at h
        subst h
        have hiff := fun a ha b hb =>
          proj_eq_iff_of_presChangeCheck hchk add (a := a) (b := b) ha hb
        refine ⟨fun h => by simp at h, by simpa [hP] using he.pres_some, he.obj_none,
          fun v hv => ?_, fun v => ?_⟩
        · obtain ⟨f, hinj, hmaps, -⟩ := he.fwd v hv
          obtain ⟨φ, hφi, hφm, -⟩ := exists_proj_injOn (A := {τ | AllHold τ s.db ∧
            objValue s.obj τ ≤ v}) fun a ha b hb =>
            hiff a (allHold_mono hinv.sub ha.1) b (allHold_mono hinv.sub hb.1)
          refine ⟨Sum.map φ id ∘ f, Set.InjOn.comp ?_ hinj hmaps, Set.MapsTo.comp ?_ hmaps,
            fun h => by simp at h⟩
          · rintro (a | a) (⟨_, ha, ⟨⟩⟩ | ⟨_, -, ⟨⟩⟩) (b | b) (⟨_, hb, ⟨⟩⟩ | ⟨_, -, ⟨⟩⟩) hab <;>
              simp only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
                id] at hab
            · rw [hP] at ha hb
              exact congrArg _ (hφi ha hb hab)
            · exact congrArg _ hab
          · rintro _ (⟨_, hl, rfl⟩ | ⟨k, hk, rfl⟩)
            · rw [hP] at hl
              exact .inl ⟨_, hφm hl, rfl⟩
            · exact .inr ⟨k, hk, rfl⟩
        · obtain ⟨g, hinj, hmaps, -⟩ := he.bwd v
          obtain ⟨ψ, hψi, hψm, -⟩ := exists_proj_injOn (A := {τ | s.chk = true ∧
            AllHold τ s.core ∧ objValue s.obj τ ≤ v}) fun a ha b hb =>
            (hiff a ha.2.1 b hb.2.1).symm
          have hsub : Set.MapsTo (Sum.map ψ id) (State.bwdSource { s with
              pres := some (if add = true then P.insert x else P.filter (· != x)),
              presChanged := true, next := n' } v) (s.bwdSource v) := by
            rintro _ (⟨_, hl, rfl⟩ | ⟨k, hk, rfl⟩)
            · refine .inl ⟨_, ?_, rfl⟩
              rw [hP]
              exact hψm hl
            · exact .inr ⟨k, hk, rfl⟩
          refine ⟨g ∘ Sum.map ψ id, Set.InjOn.comp hinj ?_ hsub, Set.MapsTo.comp hmaps hsub,
            fun h => by simp at h⟩
          rintro (a | a) (⟨_, ha, ⟨⟩⟩ | ⟨_, -, ⟨⟩⟩) (b | b) (⟨_, hb, ⟨⟩⟩ | ⟨_, -, ⟨⟩⟩) hab <;>
            simp only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
              id] at hab
          · exact congrArg _ (hψi ha hb hab)
          · exact congrArg _ hab
      · cases h
    · cases h
  rcases hlog with ⟨ρ, rfl⟩ | hlog
  · -- `solx`: the projection it logs moves from the solutions to the log.
    simp only [stepTop] at h
    split at h
    · rename_i Q hQ hobj0
      split at h
      · rename_i hok
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
        obtain ⟨⟨⟨hchk, hpc0⟩, hsol⟩, -⟩ := hok
        have hρ : AllHold (assignOf ρ) s.core := fun e he =>
          holds_of_solves hsol (List.mem_map_of_mem (f := (·.2)) (hinv.sub e he))
        have hP : s.pres.getD [] = Q := by rw [hQ]; rfl
        refine ⟨he.pres_eq, he.pres_some, he.obj_none, fun v hv => ?_, fun v => ?_⟩
        · obtain ⟨f, hinj, hmaps, hid⟩ := he.fwd v (by
            rcases hv with hv | hv
            · refine .inl fun d hd => ?_
              obtain ⟨d', hd', hle⟩ := hdb d hd
              exact (hv d' hd').trans_le hle
            · exact .inr hv)
          classical
          let g : List Bool ⊕ ℕ → List Bool ⊕ ℕ := fun y => match y with
            | .inl l => if l = proj Q (assignOf ρ) then .inr s.logged.length else .inl l
            | .inr k => .inr k
          have hgm : Set.MapsTo g (s.fwdTarget v) (State.fwdTarget { (s.log F obj ρ).addCore
              (exclusion Q ρ) with logged := proj Q (assignOf ρ) :: s.logged } v) := by
            rintro _ (⟨_, ⟨τ, ⟨hτ, hτv⟩, rfl⟩, rfl⟩ | ⟨k, ⟨hk, d, hd, hdv⟩, rfl⟩)
            · rw [hP]
              by_cases hl : proj Q τ = proj Q (assignOf ρ)
              · simp only [g, hl, ↓reduceIte]
                refine .inr ⟨_, ⟨by simp, ?_⟩, rfl⟩
                obtain ⟨d', hd', hle⟩ := lowerTo_le s.dbound (objValue s.obj (assignOf ρ))
                refine ⟨d', hd', ?_⟩
                simp only [hobj0, objValue] at hle hτv
                omega
              · simp only [g, hl, ↓reduceIte]
                refine .inl ⟨_, ⟨τ, ⟨List.forall_mem_cons.2 ⟨(holds_exclusion _ _ _).2 hl, hτ⟩,
                  hτv⟩, congrArg (fun P => proj P τ) hP⟩, rfl⟩
            · refine .inr ⟨k, ⟨by simp; omega, ?_⟩, rfl⟩
              obtain ⟨d', hd', hle⟩ := exists_mem_lowerTo (objValue s.obj (assignOf ρ))
                ⟨d, hd, le_rfl⟩
              exact ⟨d', hd', hle.trans hdv⟩
          have hgi : Set.InjOn g (s.fwdTarget v) := by
            rintro (a | a) ha (b | b) hb hab
            · by_cases hla : a = proj Q (assignOf ρ) <;> by_cases hlb : b = proj Q (assignOf ρ) <;>
                simp_all [g]
            · rcases hb with ⟨_, -, ⟨⟩⟩ | ⟨k, ⟨hk, -⟩, hkb⟩
              cases hkb
              by_cases hla : a = proj Q (assignOf ρ) <;> simp_all [g]
            · rcases ha with ⟨_, -, ⟨⟩⟩ | ⟨k, ⟨hk, -⟩, hka⟩
              cases hka
              by_cases hlb : b = proj Q (assignOf ρ) <;> simp_all [g]
            · simp_all [g]
          refine ⟨g ∘ f, hgi.comp hinj hmaps, hgm.comp hmaps, fun hpc l hl m hm => ?_⟩
          rcases hfl : f l with a | k
          · rw [Function.comp_apply, hfl] at hm
            by_cases hla : a = proj Q (assignOf ρ) <;> simp only [g, hla, ↓reduceIte,
              reduceCtorEq, Sum.inl.injEq] at hm
            exact hm ▸ hid hpc l hl a hfl
          · simp [Function.comp_apply, hfl, g] at hm
        · obtain ⟨g, hinj, hmaps, hid⟩ := he.bwd v
          classical
          let h' : List Bool ⊕ ℕ → List Bool ⊕ ℕ := fun y => match y with
            | .inl m => .inl m
            | .inr k => if k = s.logged.length then .inl (proj Q (assignOf ρ)) else .inr k
          have hsrc : ∀ τ, AllHold τ ((s.log F obj ρ).addCore (exclusion Q ρ)).core →
              AllHold τ s.core ∧ proj Q τ ≠ proj Q (assignOf ρ) := fun τ hτ =>
            ⟨fun e he => hτ e (List.mem_cons_of_mem _ he),
              (holds_exclusion _ _ _).1 (hτ _ List.mem_cons_self)⟩
          have hm' : Set.MapsTo h' (State.bwdSource { (s.log F obj ρ).addCore
              (exclusion Q ρ) with logged := proj Q (assignOf ρ) :: s.logged } v)
              (s.bwdSource v) := by
            rintro _ (⟨_, ⟨τ, ⟨hc, hτ, hτv⟩, rfl⟩, rfl⟩ | ⟨k, ⟨hk, h0⟩, rfl⟩)
            · exact .inl ⟨_, ⟨τ, ⟨hc, (hsrc τ hτ).1, hτv⟩, rfl⟩, rfl⟩
            · simp only [List.length_cons] at hk
              by_cases hkl : k = s.logged.length
              · simp only [h', hkl, ↓reduceIte]
                refine .inl ⟨_, ⟨assignOf ρ, ⟨hchk, hρ, ?_⟩, ?_⟩, rfl⟩
                · simp only [hobj0, objValue]
                  exact h0
                · rw [hP]
              · simp only [h', hkl, ↓reduceIte]
                exact .inr ⟨k, ⟨by omega, h0⟩, rfl⟩
          have hi' : Set.InjOn h' (State.bwdSource { (s.log F obj ρ).addCore
              (exclusion Q ρ) with logged := proj Q (assignOf ρ) :: s.logged } v) := by
            have hne : ∀ a, Sum.inl a ∈ State.bwdSource { (s.log F obj ρ).addCore
                (exclusion Q ρ) with logged := proj Q (assignOf ρ) :: s.logged } v →
                a ≠ proj Q (assignOf ρ) := by
              rintro a (⟨_, ⟨τ, ⟨-, hτ, -⟩, rfl⟩, hτa⟩ | ⟨_, -, ⟨⟩⟩)
              cases hτa
              change proj (s.pres.getD []) τ ≠ _
              rw [hP]
              exact (hsrc τ hτ).2
            rintro (a | a) ha (b | b) hb hab
            · simpa [h'] using hab
            · have := hne a ha
              by_cases hb' : b = s.logged.length <;> simp_all [h']
            · have := hne b hb
              by_cases ha' : a = s.logged.length <;> simp_all [h']
            · by_cases ha' : a = s.logged.length <;> by_cases hb' : b = s.logged.length <;>
                simp_all [h']
          refine ⟨g ∘ h', hinj.comp hi' hm', hmaps.comp hm', fun hpc m hm => ?_⟩
          exact hid hpc0 m (hm' hm)
      · cases h
    · cases h
  · -- Any other step: the injections carry over.
    refine injInv_of_frame he hdb hobj hpres hpc (fun v hv => ?_) fun v => ?_
    · rintro _ (⟨_, ⟨τ, ⟨hτ, hτv⟩, rfl⟩, rfl⟩ | ⟨k, ⟨hk, d, hd, hdv⟩, rfl⟩)
      · rcases stepTop_fwd hinv hord h hτ with ⟨τ', hτ', hle, hp⟩ | ⟨⟨d', hd', hle⟩, hcut⟩
        · refine .inl ⟨_, ⟨τ', ⟨hτ', hle.trans hτv⟩, ?_⟩, rfl⟩
          rw [hpres]
          exact proj_getD hp
        · rcases hv with hv | hv
          · exact absurd (hv d' hd') (not_lt.2 (hle.trans hτv))
          · obtain ⟨P, -, hP⟩ := hcut (he.obj_none hv)
            rw [hlog] at hP
            exact absurd hP (List.cons_ne_self _ _).symm
      · refine .inr ⟨k, ⟨hlog ▸ hk, ?_⟩, rfl⟩
        obtain ⟨d', hd', hle⟩ := hdb d hd
        exact ⟨d', hd', hle.trans hdv⟩
    · rintro _ (⟨_, ⟨τ, ⟨hc, hτ, hτv⟩, rfl⟩, rfl⟩ | ⟨k, hk, rfl⟩)
      · obtain ⟨hc₀, τ₀, hτ₀, hle, hp⟩ := stepTop_back hinv hord.loaded h hc hτ
        refine .inl ⟨_, ⟨τ₀, ⟨hc₀, hτ₀, hle.trans hτv⟩, ?_⟩, rfl⟩
        rw [hpres]
        exact proj_getD hp
      · exact .inr ⟨k, hlog ▸ hk, rfl⟩

/-- **The invariants of a run.** The state after running the steps from the formula `F`, the
objective `obj` and the preserved set `pres` meets the core invariant and the counting
injections. -/
theorem invariants_of_runTop {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {ss : List TopStep} {s : State}
    (h : runTop F obj (State.init F obj pres) ss = some s) :
    Inv F obj s ∧ InjInv F obj pres s :=
  have hie := runTop_induct (P := fun s => Inv F obj s ∧ OrdInv s ∧ InjInv F obj pres s)
    (fun _ _ _ hs ht => ⟨stepTop_inv hs.1 hs.2.1.loaded ht, stepTop_ordInv hs.1 hs.2.1 ht,
      stepTop_injInv hs.1 hs.2.1 hs.2.2 ht⟩) _ _ s
    ⟨inv_init F obj pres, ordInv_init F obj pres, injInv_init F obj pres⟩ h
  ⟨hie.1, hie.2.2⟩

/-- A run without `preserved_add` and `preserved_rm` steps leaves the preserved set unchanged. -/
theorem presChanged_of_runTop {F : List PBConstr} {obj : Option Objective} :
    ∀ {s : State} {ss : List TopStep} {s' : State},
      (∀ t ∈ ss, ∀ add x c sub, t ≠ .presChange add x c sub) → s.presChanged = false →
      runTop F obj s ss = some s' → s'.presChanged = false
  | s, [], s', _, hs, h => by
    simp only [runTop, Option.some.injEq] at h
    exact h ▸ hs
  | s, t :: ss, s', hss, hs, h => by
    simp only [runTop] at h
    split at h
    · rename_i s₁ h₁
      refine presChanged_of_runTop (fun t' ht' => hss t' (List.mem_cons_of_mem _ ht')) ?_ h
      rcases (stepTop_frame h₁).2.2 with ⟨add, x, c, sub, rfl⟩ | ⟨-, hpc⟩
      · exact absurd rfl (hss _ List.mem_cons_self add x c sub)
      · exact hpc ▸ hs
    · cases h

/-- **The lower-bound invariant from the forward injection**: for a solution `σ` of the formula,
some solution of the database has value at most that of `σ`, or `dbound` is at most it. -/
theorem InjInv.reaches {F : List PBConstr} {obj : Option Objective} {pres : Option (List ℕ)}
    {s : State} (he : InjInv F obj pres s) {σ : ℕ → Bool} (hσ : ∀ c ∈ F, c.Holds σ) :
    Reaches (objValue obj σ) s := by
  by_cases hd : ∃ d ∈ s.dbound, d ≤ objValue obj σ
  · exact .inr hd
  push Not at hd
  obtain ⟨f, -, hmaps, -⟩ := he.fwd _ (.inl hd)
  rcases hmaps ⟨σ, ⟨hσ, le_rfl⟩, rfl⟩ with ⟨_, ⟨τ, hτ, -⟩, -⟩ | ⟨k, ⟨-, d, hd', hle⟩, -⟩
  · exact .inl ⟨τ, hτ⟩
  · exact absurd (hd d hd') (not_lt.2 hle)

/-- **The backward existence from the backward injection**: while no unchecked deletion has
happened, every solution of the core set gives a solution of the formula of no larger value. -/
theorem InjInv.exists_of_core {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {s : State} (he : InjInv F obj pres s) (hc : s.chk = true)
    {τ : ℕ → Bool} (hτ : AllHold τ s.core) :
    ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ objValue s.obj τ := by
  obtain ⟨g, -, hmaps, -⟩ := he.bwd (objValue s.obj τ)
  obtain ⟨σ, hσ, -⟩ := hmaps (.inl ⟨_, ⟨τ, ⟨hc, hτ, le_rfl⟩, rfl⟩, rfl⟩)
  exact ⟨σ, hσ⟩

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
    obtain ⟨hinv, he⟩ := invariants_of_runTop hrun
    exact ⟨s, h, hinv, fun σ hσF => he.reaches hσF⟩
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
@[expose]
def projections (F : List PBConstr) (P : List ℕ) : Set (List Bool) :=
  {l | ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ proj P σ = l}

/-- The final state of an accepted proof meets the counting injections. -/
private theorem enum_of_checkRed {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    (h : checkRed F obj P pres = true) :
    ∃ s, checkConclusion F obj s P.conclusion = true ∧ InjInv F obj pres s := by
  unfold checkRed at h
  split at h
  · rename_i s hrun
    exact ⟨s, h, (invariants_of_runTop hrun).2⟩
  · cases h

/-- An accepted `ENUMERATION` conclusion needs a preserved set. -/
theorem isSome_of_checkRed_enum {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {n : ℕ} (h : checkRed F obj P pres = true)
    (hc : P.conclusion = .enumPartial n ∨ ∃ q, P.conclusion = .enumComplete n q) :
    pres.isSome := by
  obtain ⟨s, hconc, he⟩ := enum_of_checkRed h
  rw [← he.pres_some]
  rcases hc with hc | ⟨q, hc⟩ <;> rw [hc] at hconc <;>
    simp only [checkConclusion, Bool.and_eq_true] at hconc
  · exact hconc.1.2
  · exact hconc.1.1.2

/-- Without an objective, the solutions of value at most `0` are all the solutions. -/
private theorem image_solsLE_none (F : List PBConstr) (P : List ℕ) :
    proj P '' solsLE F none 0 = projections F P := by
  ext l
  simp [solsLE, projections, objValue]

/-- **Soundness of the enumeration count**: if the checker accepts
`conclusion ENUMERATION_PARTIAL n` or `conclusion ENUMERATION_COMPLETE n : q` for the formula
`F` with the preserved set `Pres`, then `F` has at least `n` solutions with distinct projections
to `Pres`: the backward injection maps the `n` logged indices injectively into them. -/
theorem le_encard_of_checkRed_enum {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {Pres : List ℕ} {n : ℕ} (h : checkRed F obj P (some Pres) = true)
    (hc : P.conclusion = .enumPartial n ∨ ∃ q, P.conclusion = .enumComplete n q) :
    (n : ℕ∞) ≤ (projections F Pres).encard := by
  obtain ⟨s, hconc, he⟩ := enum_of_checkRed h
  have hlen : obj = none ∧ s.logged.length = n := by
    rcases hc with hc | ⟨q, hc⟩ <;> rw [hc] at hconc <;>
      simp only [checkConclusion, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none]
        at hconc
    · exact ⟨hconc.1.1, hconc.2⟩
    · exact ⟨hconc.1.1.1, hconc.1.2⟩
  obtain ⟨rfl, hlen⟩ := hlen
  obtain ⟨g, hinj, hmaps, -⟩ := he.bwd 0
  have hsub : Sum.inr '' {k | k < s.logged.length} ⊆ s.bwdSource 0 := by
    rintro _ ⟨k, hk, rfl⟩
    exact .inr ⟨k, ⟨hk, le_rfl⟩, rfl⟩
  calc (n : ℕ∞) = (Sum.inr '' {k | k < s.logged.length} : Set (List Bool ⊕ ℕ)).encard := by
        rw [Sum.inr_injective.injOn.encard_image, Set.Nat.encard_range, hlen]
    _ ≤ (proj Pres '' solsLE F none 0).encard :=
        Set.encard_le_encard_of_injOn (hmaps.mono_left hsub) (hinj.mono hsub)
    _ = _ := by rw [image_solsLE_none]

/-- **Soundness of a complete enumeration**: if the checker accepts
`conclusion ENUMERATION_COMPLETE n : q` for the formula `F` with the preserved set `Pres`, then
the solutions of `F` have exactly `n` distinct projections to `Pres`: the database has no
solution, so the forward injection maps them injectively into the `n` logged indices. -/
theorem encard_eq_of_checkRed_enumComplete {F : List PBConstr} {obj : Option Objective}
    {P : RedProof} {Pres : List ℕ} {n q : ℕ} (h : checkRed F obj P (some Pres) = true)
    (hc : P.conclusion = .enumComplete n q) : (projections F Pres).encard = n := by
  refine le_antisymm ?_ (le_encard_of_checkRed_enum h (.inr ⟨q, hc⟩))
  obtain ⟨s, hconc, he⟩ := enum_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hconc
  obtain ⟨⟨⟨rfl, -⟩, hlen⟩, hq⟩ := hconc
  obtain ⟨f, hinj, hmaps, -⟩ := he.fwd 0 (.inr rfl)
  have hsub : s.fwdTarget 0 ⊆ Sum.inr '' {k | k < s.logged.length} := by
    rintro _ (⟨_, ⟨τ, ⟨hτ, -⟩, -⟩, -⟩ | ⟨k, ⟨hk, -⟩, rfl⟩)
    · simp [hτ.not_namesContra] at hq
    · exact ⟨k, hk, rfl⟩
  calc (projections F Pres).encard = (proj Pres '' solsLE F none 0).encard := by
        rw [image_solsLE_none]
    _ ≤ (Sum.inr '' {k | k < s.logged.length} : Set (List Bool ⊕ ℕ)).encard :=
        Set.encard_le_encard_of_injOn (hmaps.mono_right hsub) hinj
    _ = n := by rw [Sum.inr_injective.injOn.encard_image, Set.Nat.encard_range, hlen]

/-! ### Proofs without redundance and solutions -/

theorem runTop_map_step (F : List PBConstr) (obj : Option Objective) (s : State)
    (hs : s.tcb = false) (ho : s.order = none) (ss : List Step) :
    (runTop F obj s (ss.map .step)).map (fun s' => (s'.db, s'.dbound)) =
      (runSteps s.db s.next ss).map fun p => (p.1, s.dbound) := by
  induction ss generalizing s with
  | nil => rfl
  | cons st ss ih =>
    simp only [List.map_cons, runTop, runSteps, stepTop]
    rcases h : runStep s.db s.next st with _ | ⟨db', n'⟩
    · simp
    · simp only [hs, ho, Option.isSome_none, Bool.or_self, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte]
      exact ih _ rfl rfl

/-- On proofs of `UNSAT` without `red` and solutions, the checker is the checker of
implicational steps. -/
theorem checkRed_map_step (F : List PBConstr) (obj : Option Objective) (P : Proof) :
    checkRed F obj ⟨P.steps.map .step, .unsat P.conclusion⟩ = check F P := by
  have hmap := runTop_map_step F obj (State.init F obj none) rfl rfl P.steps
  unfold checkRed check
  simp only [State.init] at hmap ⊢
  rcases h1 : runTop F obj
      ⟨initDb F, F.length + 1, none, none, initDb F, true, false, obj, none, [], [], none, none,
        false⟩
      (P.steps.map .step) with _ | s <;>
    rcases h2 : runSteps (initDb F) (F.length + 1) P.steps with _ | ⟨db, n⟩ <;>
    simp_all [checkConclusion]

end VeriPB

end Cslib.Logic.PL

end
