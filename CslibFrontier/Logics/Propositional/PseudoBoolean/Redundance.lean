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
`Cslib.Logic.PL.VeriPB.Objective.improving`).

The checker keeps two logged solutions (`Cslib.Logic.PL.VeriPB.State`), as CakePB keeps
`dbound` and `bound` (`update_dbound`, `update_bound` and `check_hconcl` in
`npbc_checkScript.sml`). The best logged solution gives the value that the lower bounds are
checked against. The witness, the best logged solution that also solves the input formula,
certifies `SAT` and finite upper bounds. A logged solution that does not solve the input formula
never displaces the witness, even on a tie.

**Conclusions** (§4.3; `Cslib.Logic.PL.VeriPB.Conclusion`). `UNSAT : q` needs a contradiction `q`
and no logged solution. `SAT` needs a witness. `BOUNDS lb : q ub` needs an objective; the lower
bound `lb` must be at most the best logged value, and `q` must be a contradiction or weakly
syntactically imply `f ≥ lb`; `lb = INF` is checked as `UNSAT`. The upper bound `ub`, unless
`INF`, must be the value of the witness; see **Deletion** below. §4.3 gives `BOUNDS` for
optimization problems; accepting `UNSAT` and `SAT` under an objective as well is an extension of
this checker.

**The invariant** (`Cslib.Logic.PL.VeriPB.Reaches`, `Cslib.Logic.PL.VeriPB.runTop_reaches`).
For a value `w`, either some solution of the database has objective at most `w`, or the best
logged solution does. Every step keeps this: an implicational step keeps every solution, a
deletion enlarges the set of solutions, a `red` step repairs a solution without raising the
objective, and `soli ρ` removes only solutions of objective at least `f(ρ)`, which the logged
`ρ` matches. Every solution `σ` of the formula meets the invariant initially for `w = f(σ)`,
which gives the lower bounds; the logged solution gives the upper bound. This is the invariant
`bimp_obj` of CakePB (`npbc_checkScript.sml`, `check_csteps_correct`, CakeML commit `14856fcf`),
whose semantics of conclusions (`sem_concl`, `npbcScript.sml`) the soundness theorems follow.

**Deletion.** Deletion is the untyped deletion of `Cslib.Logic.PL.VeriPB.Step.del`, with no
core/derived distinction, so every deletion is unchecked. Unchecked deletion enlarges the set of
solutions, which keeps the invariant, but a solution of the database need not then solve the
input formula. VeriPB and CakePB certify upper bounds and `SAT` only from solutions logged while
no unchecked deletion has happened; here, instead, a logged solution is checked against the
input formula when it is logged, and only one that passes can become the witness
(`Cslib.Logic.PL.VeriPB.State.log`, `Cslib.Logic.PL.VeriPB.runTop_witness`). This is sound
whatever was deleted.

**Scope.** There is no order, so no dominance and no order goals; no checked deletion, `core`
set or strengthening-to-core mode; and none of `solx`, `obji` and the objective update `obju`
(§5.9), whose proof goals must be derived from the core set alone, which this checker does not
track. The conclusions `NONE` and `ENUMERATION`, and the optional assignments of `SAT` and
`BOUNDS`, are not supported. Matching VeriPB, `red` steps are not cutting-planes steps, and the
translation of `Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check` covers only proofs without
them.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Witness`, `Cslib.Logic.PL.VeriPB.Witness.substC`: witnesses and
  substitution.
* `Cslib.Logic.PL.VeriPB.Objective`, `Cslib.Logic.PL.VeriPB.objGoal`: objectives and the
  objective goal of `red`.
* `Cslib.Logic.PL.VeriPB.TopStep`, `Cslib.Logic.PL.VeriPB.Conclusion`,
  `Cslib.Logic.PL.VeriPB.RedProof`, `Cslib.Logic.PL.VeriPB.checkRed`: proofs with `red` and
  solution-logging steps, their conclusions, and their checker.

## Main results

* `Cslib.Logic.PL.VeriPB.Witness.holds_substC`: `σ ⊨ D|ω` iff `σ ∘ ω ⊨ D`.
* `Cslib.Logic.PL.VeriPB.redCheck_sound`: a checked `red` step repairs a solution of the database
  without raising the objective.
* `Cslib.Logic.PL.VeriPB.runTop_reaches`: the invariant.
* `Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_cnf_of_checkRed`: soundness for `UNSAT`.
* `Cslib.Logic.PL.VeriPB.exists_satisfies_of_checkRed`: soundness for `SAT`.
* `Cslib.Logic.PL.VeriPB.le_eval_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed_bounds`,
  `Cslib.Logic.PL.VeriPB.exists_eval_eq_of_checkRed`: soundness for `BOUNDS`, its lower bound,
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
  /-- `red C : ω : subproof … qed [: n]`. -/
  | red (c : PBConstr) (ω : Witness) (items : List RedItem) (qed : Option ℕ)
  /-- `sol ρ`: log the solution `ρ` (§5.8.1 of the documentation). -/
  | sol (ρ : List (Literal ℕ))
  /-- `soli ρ`: log the solution `ρ` and add the objective-improving constraint (§5.8.2). -/
  | soli (ρ : List (Literal ℕ))
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

/-- The end of a `red` subproof: the closing constraint is a contradiction, or every goal is
covered. -/
def redOk (obj : Option Objective) (db₀ : List (ℕ × PBConstr)) (ω : Witness) (c : PBConstr)
    (db' : List (ℕ × PBConstr)) (proved : List PBConstr) : Option ℕ → Bool
  | some q => namesContra db' q
  | none =>
    goalCovered db₀ proved c.negate (Witness.substC ω c) &&
      obj.all (fun f => goalCovered db₀ proved c.negate (objGoal f ω)) &&
      db₀.all fun e => Witness.touchedTrue ω e.2 || weakImplies e.2 (Witness.substC ω e.2) ||
        goalCovered db₀ proved c.negate (Witness.substC ω e.2)

/-- **The redundance check** of `red C : ω` for the objective `obj`: `¬C` takes the number `n`,
the subproof runs, and then either the closing contradiction is derived, or `C|ω` is covered, so
is `f|ω ≤ f` for an objective `f`, and so is `D|ω` for every constraint `D` of the database,
`D|ω` also when `ω` sets every literal of `D` it touches true. Returns the next number after the
subproof. -/
def redCheck (obj : Option Objective) (db₀ : List (ℕ × PBConstr)) (n : ℕ) (c : PBConstr)
    (ω : Witness) (items : List RedItem) (qed : Option ℕ) : Option ℕ :=
  match runItems obj db₀ ω c ((n, c.negate) :: db₀) (n + 1) items [] with
  | none => none
  | some (db', n', proved) => if redOk obj db₀ ω c db' proved qed then some n' else none

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

/-! ### Proofs and the checker -/

/-- The state of the checker between top-level steps. -/
structure State where
  /-- The constraint database. -/
  db : List (ℕ × PBConstr)
  /-- The next constraint number. -/
  next : ℕ
  /-- The best logged solution, if any. It solved the database when it was logged; the lower
  bounds are checked against its value. -/
  best : Option (List (Literal ℕ))
  /-- The best logged solution that also solves the input formula, if any. It certifies `SAT`
  and finite upper bounds. -/
  witness : Option (List (Literal ℕ))
  deriving DecidableEq, Repr

/-- Log the solution `ρ` in the state `s` for the formula `F`: it competes for `best`, and, if it
solves `F`, for `witness`. A solution that does not solve `F` never displaces a witness. -/
def State.log (F : List PBConstr) (obj : Option Objective) (s : State) (ρ : List (Literal ℕ)) :
    State :=
  { s with best := record obj s.best ρ,
           witness := if solves ρ (F.map normalize) then record obj s.witness ρ else s.witness }

/-- Run the top-level steps for the input formula `F` and the objective `obj`. -/
def runTop (F : List PBConstr) (obj : Option Objective) : State → List TopStep → Option State
  | s, [] => some s
  | s, .step st :: ss =>
    match runStep s.db s.next st with
    | some (db', n') => runTop F obj { s with db := db', next := n' } ss
    | none => none
  | s, .red c ω items q :: ss =>
    match redCheck obj s.db s.next c ω items q with
    | some n' => runTop F obj { s with db := (n', c.normalize) :: s.db, next := n' + 1 } ss
    | none => none
  | s, .sol ρ :: ss =>
    if solves ρ (s.db.map (·.2)) then runTop F obj (s.log F obj ρ) ss
    else none
  | s, .soli ρ :: ss =>
    match obj with
    | some f =>
      if solves ρ (s.db.map (·.2)) && assigns ρ f then
        runTop F obj { s.log F obj ρ with
          db := (s.next, (f.improving (f.eval (assignOf ρ))).normalize) :: s.db,
          next := s.next + 1 } ss
      else none
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
bound: for `INF`, `q` is a contradiction and no solution was logged; otherwise `lb` is at most
the best logged value and `q` is a contradiction or weakly syntactically implies `f ≥ lb`. The
upper bound, unless `INF`: the best logged solution that solves the input formula (the witness)
has value `ub`. -/
def boundsOk (f : Objective) (s : State) (lb : Option ℤ) (q : ℕ) (ub : Option ℤ) : Bool :=
  (match lb with
    | none => s.best.isNone && namesContra s.db q
    | some l =>
      s.best.all (fun ρ => decide (l ≤ f.eval (assignOf ρ))) &&
        (namesContra s.db q || (lookup s.db q).any fun D => weakImplies D (f.atLeast l))) &&
  match ub with
  | none => true
  | some u => s.witness.any fun ρ => f.eval (assignOf ρ) == u

/-- **The check of a conclusion** for the objective `obj` in the final state `s`. `UNSAT : q`
needs the contradiction `q` and no logged solution; `SAT` a logged solution that solves the input
formula (a witness); `BOUNDS` an objective and `Cslib.Logic.PL.VeriPB.boundsOk`. `UNSAT` and
`SAT` are also accepted under an objective, an extension of this checker: §4.3 of the
documentation gives `BOUNDS` for optimization problems. -/
def checkConclusion (obj : Option Objective) (s : State) : Conclusion → Bool
  | .unsat q => s.best.isNone && namesContra s.db q
  | .sat => s.witness.isSome
  | .bounds lb q ub =>
    match obj with
    | some f => boundsOk f s lb q ub
    | none => false

/-- **The checker** for the formula `F` and the objective `obj`: run the steps from the
formula, numbered from `1`, and check the conclusion. -/
def checkRed (F : List PBConstr) (obj : Option Objective) (P : RedProof) : Bool :=
  match runTop F obj ⟨initDb F, F.length + 1, none, none⟩ P.steps with
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

/-- **The redundance check is sound**: an assignment `σ` satisfying the database is either one
satisfying `C` too, or `σ ∘ ω` satisfies the database and `C`; either way, the objective does not
increase. -/
theorem redCheck_sound {σ : ℕ → Bool} {obj : Option Objective} {db₀ : List (ℕ × PBConstr)}
    {n n' : ℕ} {c : PBConstr} {ω : Witness} {items : List RedItem} {qed : Option ℕ}
    (hdb : AllHold σ db₀) (h : redCheck obj db₀ n c ω items qed = some n') :
    ∃ τ, AllHold τ ((n', c.normalize) :: db₀) ∧ objValue obj τ ≤ objValue obj σ := by
  by_cases hc : c.Holds σ
  · exact ⟨σ, List.forall_mem_cons.2 ⟨(holds_normalize σ c).2 hc, hdb⟩, le_rfl⟩
  unfold redCheck at h
  split at h
  · cases h
  rename_i db' n'' proved hrun
  have hnegC : c.negate.Holds σ := (holds_negate σ c).2 hc
  have hneg : AllHold σ ((n, c.negate) :: db₀) := List.forall_mem_cons.2 ⟨hnegC, hdb⟩
  obtain ⟨hall, hp⟩ := runItems_sound _ _ _ [] db' n'' proved hneg (by simp) hrun
  split at h
  · rename_i hok
    cases h
    refine ⟨Witness.apply σ ω, ?_⟩
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
        · exact Witness.Holds.apply_of_touchedTrue ht (hdb e he)
        · rw [← Witness.holds_substC]; exact Holds.of_weakImplies (hdb e he) hw
        · rw [← Witness.holds_substC]; exact goalCovered_holds hdb hp hnegC hg
      · cases obj with
        | none => exact le_rfl
        | some f =>
          simp only [Option.all_some] at hobj
          exact (holds_objGoal σ f ω).1 (goalCovered_holds hdb hp hnegC hobj)
  · cases h

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

private theorem record_le {obj : Option Objective} {best : Option (List (Literal ℕ))}
    {ρ ρ' : List (Literal ℕ)} (h : ρ' ∈ record obj best ρ) :
    objValue obj (assignOf ρ') ≤ objValue obj (assignOf ρ) ∧
      ∀ ρ'' ∈ best, objValue obj (assignOf ρ') ≤ objValue obj (assignOf ρ'') := by
  unfold record at h
  split at h
  · rename_i ρ₀
    split at h <;> simp only [Option.mem_def, Option.some.injEq] at h <;> subst h <;>
      refine ⟨by omega, fun ρ'' h'' => ?_⟩ <;>
      simp only [Option.mem_def, Option.some.injEq] at h'' <;> subst h'' <;> omega
  · simp only [Option.mem_def, Option.some.injEq] at h
    subst h
    simp

/-! ### The invariant -/

/-- **The invariant** for a value `w`: some solution of the database has objective at most `w`,
or the best logged solution does. -/
def Reaches (obj : Option Objective) (w : ℤ) (s : State) : Prop :=
  (∃ τ, AllHold τ s.db ∧ objValue obj τ ≤ w) ∨
    ∃ ρ ∈ s.best, objValue obj (assignOf ρ) ≤ w

private theorem exists_record_eq (obj : Option Objective) (best : Option (List (Literal ℕ)))
    (ρ : List (Literal ℕ)) : ∃ ρ', record obj best ρ = some ρ' := by
  unfold record
  split
  · split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem exists_mem_record_le {obj : Option Objective} {best : Option (List (Literal ℕ))}
    {w : ℤ} (ρ : List (Literal ℕ)) (h : ∃ ρ₀ ∈ best, objValue obj (assignOf ρ₀) ≤ w) :
    ∃ ρ' ∈ record obj best ρ, objValue obj (assignOf ρ') ≤ w := by
  obtain ⟨ρ₀, h₀, hw⟩ := h
  obtain ⟨ρ', hr⟩ := exists_record_eq obj best ρ
  exact ⟨ρ', hr, ((record_le hr).2 ρ₀ h₀).trans hw⟩

private theorem log_witness {F : List PBConstr} {obj : Option Objective} {s : State}
    {ρ : List (Literal ℕ)} (hs : ∀ ρ' ∈ s.witness, solves ρ' (F.map normalize) = true) :
    ∀ ρ' ∈ (s.log F obj ρ).witness, solves ρ' (F.map normalize) = true := by
  intro ρ' hρ'
  simp only [State.log] at hρ'
  split at hρ'
  · rename_i hρ
    unfold record at hρ'
    split at hρ'
    · rename_i ρ₀ h₀
      split at hρ' <;> simp only [Option.mem_def, Option.some.injEq] at hρ' <;> subst hρ'
      · exact hs _ h₀
      · exact hρ
    · simp only [Option.mem_def, Option.some.injEq] at hρ'
      exact hρ' ▸ hρ
  · exact hs ρ' hρ'

/-- **The checker keeps the invariant**, for every value `w`. -/
theorem runTop_reaches {F : List PBConstr} {obj : Option Objective} {w : ℤ} :
    ∀ (s : State) (ss : List TopStep) (s' : State), Reaches obj w s →
      runTop F obj s ss = some s' → Reaches obj w s'
  | s, [], s', hs, h => by
    simp only [runTop, Option.some.injEq] at h
    exact h ▸ hs
  | s, .step st :: ss, s', hs, h => by
    simp only [runTop] at h
    split at h
    · rename_i db₁ n₁ h₁
      refine runTop_reaches _ ss s' ?_ h
      rcases hs with ⟨τ, hτ, hw⟩ | hb
      · exact .inl ⟨τ, runStep_sound _ _ _ _ _ hτ h₁, hw⟩
      · exact .inr hb
    · cases h
  | s, .red c ω items q :: ss, s', hs, h => by
    simp only [runTop] at h
    split at h
    · rename_i n₁ h₁
      refine runTop_reaches _ ss s' ?_ h
      rcases hs with ⟨τ, hτ, hw⟩ | hb
      · obtain ⟨τ', hτ', hle⟩ := redCheck_sound hτ h₁
        exact .inl ⟨τ', hτ', hle.trans hw⟩
      · exact .inr hb
    · cases h
  | s, .sol ρ :: ss, s', hs, h => by
    simp only [runTop] at h
    split at h
    · refine runTop_reaches _ ss s' ?_ h
      rcases hs with hτ | hb
      · exact .inl hτ
      · exact .inr (exists_mem_record_le ρ hb)
    · cases h
  | s, .soli ρ :: ss, s', hs, h => by
    simp only [runTop] at h
    split at h
    · rename_i f
      split at h
      · refine runTop_reaches _ ss s' ?_ h
        by_cases hlt : ∃ τ, AllHold τ s.db ∧ objValue (some f) τ ≤ w ∧
            f.eval τ < f.eval (assignOf ρ)
        · obtain ⟨τ, hτ, hw, hlt⟩ := hlt
          exact .inl ⟨τ, List.forall_mem_cons.2
            ⟨(holds_normalize _ _).2 ((Objective.holds_improving _ _ _).2 hlt), hτ⟩, hw⟩
        · rcases hs with ⟨τ, hτ, hw⟩ | hb
          · obtain ⟨ρ', hr⟩ := exists_record_eq (some f) s.best ρ
            refine .inr ⟨ρ', hr, ?_⟩
            have := (record_le hr).1
            have hge : f.eval (assignOf ρ) ≤ f.eval τ := by
              by_contra hc
              exact hlt ⟨τ, hτ, hw, by omega⟩
            simp only [objValue] at this hw ⊢
            omega
          · exact .inr (exists_mem_record_le ρ hb)
      · cases h
    · cases h

/-- **The witness solves the input formula**: the checker admits a logged solution as the
witness only if it solves `F`. -/
theorem runTop_witness {F : List PBConstr} {obj : Option Objective} :
    ∀ (s : State) (ss : List TopStep) (s' : State),
      (∀ ρ ∈ s.witness, solves ρ (F.map normalize) = true) →
      runTop F obj s ss = some s' → ∀ ρ ∈ s'.witness, solves ρ (F.map normalize) = true
  | s, [], s', hs, h => by
    simp only [runTop, Option.some.injEq] at h
    exact h ▸ hs
  | s, .step st :: ss, s', hs, h => by
    simp only [runTop] at h
    split at h
    · exact runTop_witness _ ss s' (by exact hs) h
    · cases h
  | s, .red c ω items q :: ss, s', hs, h => by
    simp only [runTop] at h
    split at h
    · exact runTop_witness _ ss s' (by exact hs) h
    · cases h
  | s, .sol ρ :: ss, s', hs, h => by
    simp only [runTop] at h
    split at h
    · exact runTop_witness _ ss s' (by exact log_witness hs) h
    · cases h
  | s, .soli ρ :: ss, s', hs, h => by
    simp only [runTop] at h
    split at h
    · split at h
      · exact runTop_witness _ ss s' (by exact log_witness hs) h
      · cases h
    · cases h

/-! ### Soundness of the conclusions -/

/-- The final state of an accepted proof meets the invariant for the value of every solution of
the formula. -/
private theorem reaches_of_checkRed {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    (h : checkRed F obj P = true) :
    ∃ s, runTop F obj ⟨initDb F, F.length + 1, none, none⟩ P.steps = some s ∧
      checkConclusion obj s P.conclusion = true ∧
      (∀ σ, (∀ c ∈ F, c.Holds σ) → Reaches obj (objValue obj σ) s) ∧
      ∀ ρ ∈ s.witness, solves ρ (F.map normalize) = true := by
  unfold checkRed at h
  split at h
  · rename_i s hrun
    exact ⟨s, hrun, h, fun σ hσ =>
      runTop_reaches _ _ s (.inl ⟨σ, allHold_initDb hσ, le_rfl⟩) hrun,
      runTop_witness _ _ s (by simp) hrun⟩
  · cases h

/-- **Soundness for `UNSAT`**: a formula with a checked proof of `UNSAT` has no solution. -/
theorem not_satisfiable_of_checkRed {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {q : ℕ} (h : checkRed F obj P = true) (hc : P.conclusion = .unsat q) (σ : ℕ → Bool) :
    ¬ ∀ c ∈ F, c.Holds σ := fun hF => by
  obtain ⟨s, -, hconc, hreach, -⟩ := reaches_of_checkRed h
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

private theorem holds_of_solves_normalize {ρ : List (Literal ℕ)} {F : List PBConstr}
    (h : solves ρ (F.map normalize) = true) : ∀ c ∈ F, c.Holds (assignOf ρ) := fun c hc =>
  (holds_normalize _ c).1 (holds_of_solves h (List.mem_map_of_mem hc))

/-- **Soundness for `SAT`**: a formula with a checked proof of `SAT` has a solution, the logged
one. -/
theorem exists_satisfies_of_checkRed {F : List PBConstr} {obj : Option Objective}
    {P : RedProof} (h : checkRed F obj P = true) (hc : P.conclusion = .sat) :
    ∃ σ, ∀ c ∈ F, c.Holds σ := by
  obtain ⟨s, -, hconc, -, hwit⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, Option.isSome_iff_exists] at hconc
  obtain ⟨ρ, hρ⟩ := hconc
  exact ⟨_, holds_of_solves_normalize (hwit ρ hρ)⟩

/-- **Soundness for the lower bound of `BOUNDS`**: if the checker accepts
`conclusion BOUNDS lb : q ub` with a finite `lb` for the formula `F` and the objective `f`, then
every solution of `F` has objective at least `lb`. -/
theorem le_eval_of_checkRed {F : List PBConstr} {f : Objective} {P : RedProof} {lb : ℤ}
    {q : ℕ} {ub : Option ℤ} (h : checkRed F (some f) P = true)
    (hc : P.conclusion = .bounds (some lb) q ub) (σ : ℕ → Bool) (hσ : ∀ c ∈ F, c.Holds σ) :
    lb ≤ f.eval σ := by
  obtain ⟨s, -, hconc, hreach, -⟩ := reaches_of_checkRed h
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
  obtain ⟨s, -, hconc, hreach, -⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, boundsOk, Bool.and_eq_true, Option.isNone_iff_eq_none] at hconc
  obtain ⟨⟨hbest, hq⟩, -⟩ := hconc
  rcases hreach σ hF with ⟨τ, hτ, -⟩ | ⟨ρ, hρ, -⟩
  · simp [hτ.not_namesContra] at hq
  · simp [hbest] at hρ

/-- **Soundness for the upper bound of `BOUNDS`**: if the checker accepts
`conclusion BOUNDS lb : q ub` with a finite `ub` for the formula `F` and the objective `f`, then
some solution of `F`, the best logged one, has objective `ub`. With the lower bound
(`Cslib.Logic.PL.VeriPB.le_eval_of_checkRed`), the optimum lies in `[lb, ub]`. -/
theorem exists_eval_eq_of_checkRed {F : List PBConstr} {f : Objective} {P : RedProof}
    {lb : Option ℤ} {q : ℕ} {ub : ℤ} (h : checkRed F (some f) P = true)
    (hc : P.conclusion = .bounds lb q (some ub)) :
    ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ f.eval σ = ub := by
  obtain ⟨s, -, hconc, -, hwit⟩ := reaches_of_checkRed h
  rw [hc] at hconc
  simp only [checkConclusion, boundsOk, Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at hconc
  obtain ⟨-, ρ, hρ, hval⟩ := hconc
  exact ⟨_, holds_of_solves_normalize (hwit ρ hρ), hval⟩

/-! ### Proofs without redundance and solutions -/

theorem runTop_map_step (F : List PBConstr) (obj : Option Objective) (db : List (ℕ × PBConstr))
    (n : ℕ) (best witness : Option (List (Literal ℕ))) (ss : List Step) :
    runTop F obj ⟨db, n, best, witness⟩ (ss.map .step) =
      (runSteps db n ss).map fun (db', n') => ⟨db', n', best, witness⟩ := by
  induction ss generalizing db n with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, runTop, runSteps]
    rcases h : runStep db n s with _ | ⟨db', n'⟩ <;> simp [ih]

/-- On proofs of `UNSAT` without `red` and solutions, the checker is the checker of
implicational steps. -/
theorem checkRed_map_step (F : List PBConstr) (obj : Option Objective) (P : Proof) :
    checkRed F obj ⟨P.steps.map .step, .unsat P.conclusion⟩ = check F P := by
  unfold checkRed check
  rw [runTop_map_step]
  rcases runSteps (initDb F) (F.length + 1) P.steps with _ | ⟨db, n⟩ <;> rfl

end VeriPB

end Cslib.Logic.PL

end
