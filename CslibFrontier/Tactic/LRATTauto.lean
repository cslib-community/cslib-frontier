/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF.Refutation
public import CslibFrontier.Logics.Propositional.CNF.LRATKernel
public meta import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF.Numbered
public meta import CslibFrontier.Algorithms.Lean.CDCL.Watched
public meta import CslibFrontier.Logics.Propositional.CNF.LRATFast
public meta import Mathlib.Util.AtomM
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# Propositional tautologies over `Prop` from LRAT certificates

`lrat_tauto` proves a goal built from `∧`, `∨`, `→`, `¬`, `↔`, `True` and `False` over arbitrary
propositions, the *atoms*, from an LRAT certificate `cert : Array LRAT.IntAction`: one generated
at elaboration time by the CDCL solver, or one supplied as `lrat_tauto using cert`. The kernel
checks the certificate; the proof uses no native evaluation, and its axioms are those of
`Cslib.Logic.PL.Proposition.eval_prop_of_checkLRATRat`.

The tactic reads the goal `P` as a proposition `A : Proposition (Fin n)` and a valuation
`v : Fin n → Prop` of its atoms, with `A.eval v ↔ P`. It then applies
`Cslib.Logic.PL.Proposition.eval_prop_of_checkLRATRat` to `A` and `v`. Its hypothesis, that
`Cslib.Logic.PL.CNF.checkLRATRat` accepts `cert` on `(imp A falsum).plaistedGreenbaumNumberedCNF`,
is proved by `decide` for the checker built for kernel reduction,
`Cslib.Logic.PL.CNF.checkLRATKernel`, and rewritten with
`Cslib.Logic.PL.CNF.checkLRATKernel_eq_checkLRATRat`. So the kernel runs that checker, and only
that run is trusted; where the certificate came from does not matter. The goals proved are the
classical tautologies, since `eval_prop_of_checkLRATRat` decides each atom classically. Without
`using`, `P` is `P₁ → ⋯ → Pₖ → G` for the goal `G` and the premises `Pᵢ` that the tactic finds
in the context or is given as `lrat_tauto [t₁, …, tₙ]` (see "Hypotheses and leaves"); the trusted
step is the same, on a larger formula.

## Reading the goal

* Leading binders whose type is not a proposition, as in `∀ (p q : Prop) (n : ℕ), …`, are
  introduced first. The hypotheses of the local context are read as premises (see below).
* `P ∧ Q`, `P ∨ Q`, `False` and an implication `P → Q` between propositions (a non-dependent
  arrow whose domain is a proposition) are read as the constructors `and`, `or`, `falsum` and
  `imp`. `Proposition` has no other constructors, so the other connectives are encoded:
  `¬P` as `imp P falsum`, `True` as `imp falsum falsum`, and `P ↔ Q` as
  `and (imp P Q) (imp Q P)`.
* `a ≠ b` is read as `¬a = b`, which it unfolds to at reducible transparency, so a hypothesis
  `h : a ≠ b` fixes the atom `a = b`. A β-redex `(fun x => P x) a` is read as `P a`.
* Every other subterm is an atom: an equation `f x = y`, an order fact `n < 3`, a dependent `∀`
  or `∃`, a definition other than `≠` that unfolds to connectives, such as `Xor' p q`. Atoms are
  numbered from `0` in order of first occurrence, left to right, in the goal and then in the
  premises, and two atoms are the same when they are definitionally equal at reducible
  transparency.

## Hypotheses and leaves

Without `using`, the tactic proves `P₁ → ⋯ → Pₖ → G` for the goal `G` and premises `Pᵢ`, read
over shared atoms, and applies the proof to the premises' proofs; nothing is reverted. The
premises are:

* the hypotheses of the local context whose types are propositions, other than implementation
  details, in the order of the context. A hypothesis that is not a propositional formula, such as
  `h : ∀ x, f x = 0`, is an atom, as such subterms of the goal are; its type may mention other
  hypotheses and variables. `lrat_tauto -hyps` leaves them out.
* the terms of `lrat_tauto [t₁, …, tₙ]`, in the order given, after the hypotheses, as `simp [..]`
  takes lemmas. Each is elaborated in the context of the goal, after its leading binders are
  introduced, and must be a proof of a proposition with no metavariables left: arguments that
  elaboration does not determine, as in `h _`, must be given. Its type, or `T` for a type
  ascription `(t : T)` as for `have h : T := t`, is read as a hypothesis's is, so
  `lrat_tauto [h a, Nat.le_total x y]` supplies the instances of `h : ∀ x, f x = 0 ∨ p x` and of
  a lemma that the tactic would not find: it instantiates no quantifier itself. The terms are used
  with `-hyps` too.
* the atoms that reflexivity proves, `a = b` by `Eq.refl` and `HEq a b` by `HEq.refl` when `a`
  and `b` are definitionally equal at instance transparency (unfolding reducible definitions and
  instances, as `simp` does when it rewrites with `eq_self_iff_true`), with that proof, as the
  leaves `tauto` closes by `rfl`. This covers `a = a` under `≠`: `a ≠ a` is read as `¬a = a`, and
  the atom `a = a` is proved. An `↔` is a connective, never an atom. No
  other tactic runs on the atoms. The leaves `tauto` closes by `assumption` are covered by the
  hypotheses: an atom that is a hypothesis `h : a`, or whose negation is one, `h : ¬a`, is fixed
  by that premise.

Premises that a certificate does not need would still cost the kernel their clauses, so they are
dropped, terms as well as hypotheses: an unused term does not appear in the proof. The solver
refutes the formula with all the premises; those with a clause among the hints of the trimmed
certificate (one of the definitional clauses of its subformulas, or the clause of its `imp` node
asserting it) are kept, the formula is read again from them alone, numbering its atoms afresh, and
the solver refutes that formula. The kernel checks the certificate for that formula. If the solver
finds the smaller formula satisfiable, which the selection does not rule out, the formula with all
the premises and its certificate are used. This selection is untrusted, like the solver. Premises
that share no atom with the goal are not dropped before solving: they can still matter, as a
contradictory pair does.

A certificate supplied with `using` refutes the formula of the goal with only the terms as
premises, `t₁ → ⋯ → tₙ → G` for `lrat_tauto [t₁, …, tₙ] using cert` and `G` without terms, and
`lrat_tauto? [t₁, …, tₙ]` prints that formula: the clause numbers of a fixed certificate should not
depend on the context, so neither the hypotheses nor the facts found by `rfl` are premises, and
no premise is dropped. Pass the hypotheses that a supplied certificate needs as terms, or revert
them.

## The certificate

The certificate refutes the numbered Plaisted–Greenbaum transformation of `imp A falsum`
(`Cslib.Logic.PL.Proposition.plaistedGreenbaumNumberedCNF`), in which the atom numbered `i` is the
DIMACS variable `i + 1` and the clauses are numbered `1, 2, …` in order. It keeps, for each
subformula, only the direction of its Tseitin definition that the subformula's polarity needs.
`lrat_tauto?` prints that formula in DIMACS form, with the atoms in comment lines, so that a SAT
solver producing LRAT proofs can refute it. The lines of a textual LRAT proof are the `addRup`,
`addEmpty` and `del` actions of the certificate; the checker rejects RAT steps, which some solvers
emit after preprocessing (CaDiCaL does not with `--plain`).

The kernel checks the certificate once, as an auxiliary lemma that the proof then cites. If it
fails, `lrat_tauto` evaluates the checker in the kernel to tell a rejected certificate from one
the kernel cannot evaluate, such as a definition from another module whose body is not exposed,
and reports which.

## Generating the certificate

Without `using`, the tactic runs the CDCL solver `Cslib.Algorithms.Lean.CDCL.solveCompact` on the
formula, in Lean's interpreter during elaboration. If the formula is satisfiable, the goal does not
follow propositionally from the premises, and the error shows an assignment of truth values to the
atoms, read as independent propositions, under which the goal's propositional structure is false
and the premises are true; when the context has propositional hypotheses, it names them. It need
not be a countermodel of the goal itself, since the atoms may not be able to take those values:
for `∀ n : ℕ, 0 + n = n`, the one atom `0 + n = n`, which the reflexivity check does not prove,
is assigned `False`. Otherwise the solver
returns a certificate, which is proved correct (`Cslib.Algorithms.Lean.CDCL.solveCompact_unsat`)
but is not trusted here: the kernel checks it as it checks a supplied one. The certificate is first
trimmed to the steps that the empty clause depends on, without the deletions, and the clauses it
adds are renumbered `n + 1, n + 2, …` after the `n` clauses of the formula, which keeps the
kernel checker's trie shallow. The untrimmed certificate is used if the result fails the
array-based checker `Cslib.Logic.PL.CNF.checkLRATFast`, evaluated in the interpreter.
`set_option trace.lrat_tauto true` reports the sizes of the formula and of the certificate and
the times taken.

The solver is a single private definition, `generateCert`. Its type,
`Cslib.Algorithms.Lean.DPLL.Result`, guarantees neither a model nor a certificate, so a replacement
must meet this contract on each formula `φ` it is given:

* a result `.sat σ` has `σ` satisfying `φ`, since the error shows `σ` on the atoms as the
  assignment under which the goal is false;
* a result `.unsat cert` has `Cslib.Logic.PL.CNF.checkLRAT φ cert = true`: `cert` reaches an
  empty-clause step through RUP additions and deletions, since that checker rejects RAT additions.

The CDCL solver meets it (`Cslib.Algorithms.Lean.CDCL.solveCompact_sat`,
`Cslib.Algorithms.Lean.CDCL.solveCompact_unsat`), and so does the DPLL solver
`Cslib.Algorithms.Lean.DPLL.solve` (`Cslib.Algorithms.Lean.DPLL.solve_sat`,
`Cslib.Algorithms.Lean.DPLL.solve_unsat`), which replaces it by changing that definition alone. A
replacement that breaks the contract still cannot prove a goal that is not a tautology, since the
kernel checks every certificate; the tactic then fails, or shows a wrong assignment.

## Main definitions

* `lrat_tauto`: close the goal, using the hypotheses, from a certificate generated by the CDCL
  solver; `lrat_tauto -hyps` without the hypotheses.
* `lrat_tauto [t₁, …, tₙ]`: the same, with the terms `tᵢ` as further premises.
* `lrat_tauto using cert`: close the goal alone from the certificate `cert`;
  `lrat_tauto [t₁, …, tₙ] using cert`, the goal with the terms as premises.
* `lrat_tauto?` and `lrat_tauto? [t₁, …, tₙ]`: print the formula that a certificate for the goal,
  with the terms as premises, must refute.

## Limitations

* `↔` is encoded by writing each side twice, so a goal that nests `↔` to depth `d` has up to
  `2 ^ d` copies of its innermost subformulas.
* The kernel check takes most of the time. With the CDCL solver's certificates, trimmed, the kernel
  checked the pigeonhole formulas for six pigeons in five holes and seven in six (certificates of
  131 and 507 steps) in about 6 and 26 to 29 seconds, the chain of 320 implications (962 clauses,
  one step) in about 2 seconds, and the distributivity of `∧` over `∨` on six disjunctions (32
  steps) and the associativity of `↔` on six atoms (68 steps) in about 2 seconds each. On goals with
  few steps most of that time goes to reading the formula, so the time grows with the number of
  clauses as well as with the number of steps and the length of the clauses the hints name. Against
  a numbered Tseitin transformation, which the tactic used before, the Plaisted–Greenbaum
  transformation halves the clauses and cut the kernel time by about a third on the chain and
  distributivity families, by 5% to 27% on `↔` and by 8% to 17% on the pigeonhole formulas for five
  and six pigeons. For seven pigeons, whose trimmed certificate grew from 461 to 507 steps, two runs
  took 26 and 29 seconds against 27. The final step, in which the kernel checks that the goal is the
  value of `A` under `v`, took under 0.3 seconds on each of these goals, finding each atom by a
  binary search on its number. The benchmark script `LRATTautoBench` in the repository's scripts
  measures these families.
* The solver runs in Lean's interpreter, and its work counts toward `maxHeartbeats`; it takes a
  small fraction of the time of the kernel check, but on the larger formulas enough heartbeats
  that `set_option maxHeartbeats` must be raised. When premises are dropped it runs twice, and the
  first run includes every propositional hypothesis of the context. On the pigeonhole formula for
  five pigeons in four holes, with twenty irrelevant hypotheses of three connectives each in the
  context, the tactic took about 1.6 seconds against 1.4 without them, the kernel time being the
  same, and about 2.1 seconds when every hypothesis was kept.
* Atoms are compared at reducible transparency only, and equations are not oriented:
  `h : b = a` does not prove the atom `a = b`, and `a ≠ b → b = c → a ≠ c` is not proved, since
  its atoms are independent. A hypothesis whose type is only definitionally equal to a formula at
  a higher transparency is an atom.
-/

public section

namespace Cslib.Tactic.LRATTauto

open Lean Meta Elab Tactic Mathlib.Tactic
open Cslib.Logic.PL

/-- `lrat_tauto` closes a goal built from `∧`, `∨`, `→`, `¬`, `↔`, `True` and `False` over
arbitrary propositions, from an LRAT certificate that refutes the numbered Plaisted–Greenbaum
transformation of the negated goal. The certificate is generated by the CDCL solver at
elaboration time, or supplied as `lrat_tauto using cert` with `cert : Array LRAT.IntAction`; when
the goal does not follow propositionally from the hypotheses, the error shows an assignment to the
atoms, read as independent propositions, under which it is false and they are true. The kernel
checks the certificate by evaluating `Cslib.Logic.PL.CNF.checkLRATKernel`. Leading binders over
non-propositions, such as `∀ p q : Prop`, are introduced first. `a ≠ b` is read as `¬a = b`. The
atoms are the maximal subterms that are not connectives, compared at reducible transparency.

Without `using`, the propositional hypotheses of the context are premises, then the terms of
`lrat_tauto [t₁, …, tₙ]`, proofs of propositions that must elaborate without metavariables, with
the equations and `HEq`s that `rfl` proves at instance transparency; the premises that the
certificate does not need are dropped before the kernel check. `lrat_tauto -hyps` does not use
the hypotheses.

A supplied certificate refutes the formula of the goal with the terms alone as premises. It is a
closed term the kernel can evaluate: a literal, or a definition whose body it can unfold. A
certificate the checker rejects is reported as such.

`lrat_tauto? [t₁, …, tₙ]` prints the formula a supplied certificate must refute, in DIMACS
form. -/
syntax (name := lratTauto) "lrat_tauto" Lean.Parser.Tactic.optConfig
    (" [" withoutPosition(term,*) "]")? (" using " term)? : tactic

/-- `lrat_tauto?` prints the formula that a certificate for `lrat_tauto using` must refute: the
numbered Plaisted–Greenbaum transformation of the negated goal in DIMACS form, preceded by comment
lines naming the variable of each atom. `lrat_tauto? [t₁, …, tₙ]` prints the formula of
`t₁ → ⋯ → tₙ → G` for the goal `G`, which `lrat_tauto [t₁, …, tₙ] using` takes. It leaves the
goal unchanged. -/
syntax (name := lratTautoQuery) "lrat_tauto?" (" [" withoutPosition(term,*) "]")? : tactic

/- `lrat_tauto?` only prints, so the unused tactic linter would flag every use. -/
allow_unused_tactic Cslib.Tactic.LRATTauto.lratTautoQuery

meta section

open Std.Tactic.BVDecide (LRAT.IntAction LRAT.Action)

/-- A goal read as a propositional formula. An atom keeps its index and the expression it was
read from. -/
private inductive Shape where
  | atom (i : ℕ) (e : Expr)
  | falsum
  | verum
  | and (a b : Shape)
  | or (a b : Shape)
  | imp (a b : Shape)
  | not (a : Shape)
  | iff (a b : Shape)

/-- `partial` definitions returning formulas need a default one. -/
private instance : Inhabited Shape := ⟨.falsum⟩

/-- Reads a proposition as a formula over its atoms. `a ≠ b` is read as `¬a = b`, which it
unfolds to at reducible transparency, and a β-redex `(fun x => P x) a` as `P a`. -/
private partial def reify (e : Expr) : AtomM Shape := do
  let e := e.consumeMData.headBeta
  match e.getAppFnArgs with
  | (``False, #[]) => return .falsum
  | (``True, #[]) => return .verum
  | (``And, #[a, b]) => return .and (← reify a) (← reify b)
  | (``Or, #[a, b]) => return .or (← reify a) (← reify b)
  | (``Not, #[a]) => return .not (← reify a)
  | (``Ne, #[α, a, b]) =>
    return .not (← reify (mkApp3 (mkConst ``Eq e.getAppFn.constLevels!) α a b))
  | (``Iff, #[a, b]) => return .iff (← reify a) (← reify b)
  | _ =>
    if let .forallE _ a b _ := e then
      if !b.hasLooseBVars && (← isProp a) then
        return .imp (← reify a) (← reify b)
    return .atom (← AtomM.addAtom e).1 e

/-- The formula as a `Proposition` over `Fin n`, with the encodings of `¬`, `True` and `↔`. -/
private def Shape.toProposition (n : ℕ) : Shape → Proposition (Fin n)
  | .atom i _ => if h : i < n then .atom ⟨i, h⟩ else .falsum
  | .falsum => .falsum
  | .verum => .imp .falsum .falsum
  | .and a b => .and (a.toProposition n) (b.toProposition n)
  | .or a b => .or (a.toProposition n) (b.toProposition n)
  | .imp a b => .imp (a.toProposition n) (b.toProposition n)
  | .not a => .imp (a.toProposition n) .falsum
  | .iff a b =>
    let a := a.toProposition n
    let b := b.toProposition n
    .and (.imp a b) (.imp b a)

/-- A `Proposition` over `Fin n` as an expression. -/
private def propositionToExpr {n : ℕ} : Proposition (Fin n) → Expr
  | .atom i => mkApp2 (mkConst ``Proposition.atom [0]) (toTypeExpr (Fin n)) (toExpr i)
  | .falsum => mkApp (mkConst ``Proposition.falsum [0]) (toTypeExpr (Fin n))
  | .and a b => mkApp3 (mkConst ``Proposition.and [0]) (toTypeExpr (Fin n))
    (propositionToExpr a) (propositionToExpr b)
  | .or a b => mkApp3 (mkConst ``Proposition.or [0]) (toTypeExpr (Fin n))
    (propositionToExpr a) (propositionToExpr b)
  | .imp a b => mkApp3 (mkConst ``Proposition.imp [0]) (toTypeExpr (Fin n))
    (propositionToExpr a) (propositionToExpr b)

/-- For a formula, the proposition `X` that its encoding evaluates to, definitionally, under the
valuation sending each atom to the expression it was read from; the proposition `P` it was read
from; and a proof of `X ↔ P`. -/
private partial def Shape.iffGoal : Shape → MetaM (Expr × Expr × Expr)
  | .atom _ e => return (e, e, mkApp (mkConst ``Iff.refl) e)
  | .falsum =>
    return (mkConst ``False, mkConst ``False, mkApp (mkConst ``Iff.refl) (mkConst ``False))
  | .verum => do
    let x ← mkArrow (mkConst ``False) (mkConst ``False)
    let pf ← mkAppM ``iff_true_intro #[.lam `h (mkConst ``False) (.bvar 0) .default]
    return (x, mkConst ``True, pf)
  | .and a b => do
    let (xa, pa, ha) ← a.iffGoal
    let (xb, pb, hb) ← b.iffGoal
    return (mkAnd xa xb, mkAnd pa pb, ← mkAppM ``and_congr #[ha, hb])
  | .or a b => do
    let (xa, pa, ha) ← a.iffGoal
    let (xb, pb, hb) ← b.iffGoal
    return (mkOr xa xb, mkOr pa pb, ← mkAppM ``or_congr #[ha, hb])
  | .imp a b => do
    let (xa, pa, ha) ← a.iffGoal
    let (xb, pb, hb) ← b.iffGoal
    return (← mkArrow xa xb, ← mkArrow pa pb, ← mkAppM ``imp_congr #[ha, hb])
  | .not a => do
    let (xa, pa, ha) ← a.iffGoal
    return (mkNot xa, mkNot pa, ← mkAppM ``not_congr #[ha])
  | .iff a b => do
    let (xa, pa, ha) ← a.iffGoal
    let (xb, pb, hb) ← b.iffGoal
    let x := mkAnd (← mkArrow xa xb) (← mkArrow xb xa)
    let congr ← mkAppM ``and_congr #[← mkAppM ``imp_congr #[ha, hb], ← mkAppM ``imp_congr #[hb, ha]]
    let unfold ← mkAppM ``Iff.symm #[← mkAppOptM ``iff_iff_implies_and_implies #[pa, pb]]
    return (x, mkIff pa pb, ← mkAppM ``Iff.trans #[congr, unfold])

/-- Introduces the leading binders of the goal whose type is not a proposition. -/
private partial def introNonProps (g : MVarId) : MetaM MVarId := g.withContext do
  if let .forallE _ d _ _ := (← instantiateMVars (← g.getType)).consumeMData then
    unless ← isProp d do
      return ← introNonProps (← g.intro1P).2
  return g

/-- Where a premise comes from. -/
private inductive PremiseSource where
  /-- A hypothesis of the local context. -/
  | hyp
  /-- A term given in the list `lrat_tauto [t₁, …, tₙ]`. -/
  | term
  /-- A fact about an atom, proved by `rfl`. -/
  | rfl
  deriving BEq

/-- A proof that the goal may use: a hypothesis of the local context, a term given to the tactic,
or a fact about an atom. -/
private structure Premise where
  /-- The proposition it proves. -/
  type : Expr
  /-- Its proof: the hypothesis itself, the term, or a proof by `rfl`. -/
  proof : Expr
  /-- Where it comes from. -/
  source : PremiseSource

/-- The goal and the premises read as formulas over shared atoms. -/
private structure Formula where
  /-- The goal read as a formula. -/
  goal : Shape
  /-- The premises: the hypotheses, then the terms, then the facts found by `rfl`. -/
  premises : Array Premise
  /-- The premises read as formulas, in the same order. -/
  shapes : Array Shape
  /-- The atoms, numbered in order of first occurrence in the goal, then in the premises. -/
  atoms : Array Expr

/-- The hypotheses of the local context whose types are propositions, other than implementation
details, in the order of the context. -/
private def contextPremises : MetaM (Array Premise) := do
  let mut ps := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ← isProp ty then
      ps := ps.push { type := ty, proof := d.toExpr, source := .hyp }
  return ps

/-- The terms of `lrat_tauto [t₁, …, tₙ]`, elaborated in the context of the goal, as premises in
the order given. Each must elaborate fully, with no metavariables left, to a proof of a
proposition; an elaboration error is thrown rather than recovered from with `sorry`. The premise
of a type ascription `(t : T)` is `T`, elaborated as for `have h : T := t`, rather than the type
inferred for `t`. -/
private def termPremises (ts : Array Term) : TacticM (Array Premise) :=
  withoutRecover <| ts.mapM fun t => withRef t do
    let (e, ty) ← match t with
      | `(($e : $ty)) => Tactic.runTermElab do
        let ty ← Term.withSynthesize (postpone := .yes) (Term.elabType ty)
        let e ← Term.elabTermEnsuringType e ty
        pure (e, ty)
      | _ => do
        let e ← Tactic.elabTerm t none
        pure (e, ← inferType e)
    let e ← instantiateMVars e
    let ty ← instantiateMVars ty
    if e.hasMVar || ty.hasMVar then
      throwError "lrat_tauto: the term `{t}` must elaborate fully, but it has metavariables:\
        {indentExpr e}\nof type{indentExpr ty}\nGive its arguments explicitly."
    unless ← isProp ty do
      throwError "lrat_tauto: the term `{t}` is not a proof of a proposition: its type is\
        {indentExpr ty}"
    return { type := ty, proof := e, source := .term }

/-- A proof of an atom by reflexivity, if it is an equation `a = b` or `HEq a b` whose sides are
definitionally equal at instance transparency: reducible definitions and instances are unfolded,
as when `simp` rewrites with `eq_self_iff_true`. An `↔` is never an atom. -/
private def rflProof (e : Expr) : MetaM (Option Expr) :=
  withTransparency .instances <| withNewMCtxDepth do
  match e.getAppFnArgs with
  | (``Eq, #[_, a, b]) =>
    if ← isDefEq a b then return some (← mkEqRefl a)
  | (``HEq, #[α, a, β, b]) =>
    if (← isDefEq α β) && (← isDefEq a b) then return some (← mkHEqRefl a)
  | _ => pure ()
  return none

/-- The goal and the premises `ps` read as formulas over shared atoms. With `leaves`, each atom
that `rfl` proves (`rflProof`) is added after them as a premise. -/
private def readFormula (g : MVarId) (ps : Array Premise) (leaves : Bool) : MetaM Formula :=
  g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless ← isProp t do
    throwError "lrat_tauto: the goal is not a proposition:{indentExpr t}"
  AtomM.run .reducible do
    let s ← reify t
    let mut ps := ps
    let mut shapes ← ps.mapM (reify ·.type)
    if leaves then
      for (a, i) in (← get).atoms.zipIdx do
        if let some pf ← rflProof a then
          ps := ps.push { type := a, proof := pf, source := .rfl }
          shapes := shapes.push (.atom i a)
    return { goal := s, premises := ps, shapes, atoms := (← get).atoms }

/-- The formula read: `imp P₁ (imp P₂ … (imp Pₖ G))` for the premises `Pᵢ` and the goal `G`. -/
private def Formula.shape (f : Formula) : Shape := f.shapes.foldr .imp f.goal

/-- The numbered Plaisted–Greenbaum transformation of the negated formula, which the
certificate refutes. -/
private def Formula.cnf (f : Formula) : CNF ℕ :=
  (Proposition.imp (f.shape.toProposition f.atoms.size) .falsum).plaistedGreenbaumNumberedCNF

/-- The numbers that the traversal of `Proposition.plaistedGreenbaumClauses` gives to a premise:
those of its subformulas other than atoms, from `lo` to `hi - 1`; its variable; and the variable
of the `imp` node whose antecedent it is. -/
private structure PremiseVars where
  /-- The first number of its subformulas. -/
  lo : ℕ
  /-- One past the last number of its subformulas. -/
  hi : ℕ
  /-- Its variable. -/
  var : ℕ
  /-- The variable of the `imp` node of which it is the antecedent. -/
  node : ℕ

/-- The numbers of the premises `hs` in the traversal of `imp h₁ (imp h₂ … (imp hₖ G))` from
`k`, following `Proposition.plaistedGreenbaumClauses` (in post-order: the antecedent, then the
consequent, then the node), and the first number not used. -/
private def premiseVars {n : ℕ} (G : Proposition (Fin n)) :
    List (Proposition (Fin n)) → ℕ → List PremiseVars × ℕ
  | [], k => ([], k + G.plaistedGreenbaumLabels.length)
  | h :: hs, k =>
    let hi := k + h.plaistedGreenbaumLabels.length
    let var := match h with
      | .atom i => i.val
      | _ => hi - 1
    let (rest, node) := premiseVars G hs hi
    (⟨k, hi, var, node⟩ :: rest, node + 1)

/-- For each premise, whether a clause belonging to it is a hint of the certificate: one of the
definitional clauses of its subformulas, or the clause of its `imp` node asserting it. These
premises form an unsatisfiable core, up to the `imp` nodes, which the formula rebuilt from them
replaces. -/
private def usedPremises (f : Formula) (cert : Array LRAT.IntAction) : Array Bool := Id.run do
  let n := f.atoms.size
  let φ := f.cnf
  let (vars, _) := premiseVars (f.goal.toProposition n) (f.shapes.toList.map (·.toProposition n))
    n
  -- the premise of each number of a subformula, and of each `imp` node
  let mut owner : Std.HashMap ℕ ℕ := {}
  let mut node : Std.HashMap ℕ ℕ := {}
  for (pv, i) in vars.zipIdx do
    for x in [pv.lo:pv.hi] do owner := owner.insert x i
    node := node.insert pv.node i
  let clauses := φ.toArray
  let mut used := Array.replicate f.premises.size false
  for a in cert do
    let hints : Array ℕ := match a with
      | .addRup _ _ hints | .addEmpty _ hints => hints
      | .addRat _ _ _ hints _ => hints
      | .del _ => #[]
    for h in hints do
      let some c := clauses[h - 1]? | continue
      let some (x, _) := c.head? | continue
      if let some i := owner[x]? then used := used.set! i true
      if let some i := node[x]? then
        if let some pv := vars[i]? then
          if c == [(x, true), (pv.var, true)] then used := used.set! i true
  return used

/-- The DIMACS form of a formula over the variables `0, 1, …`: the variable `i` is `i + 1`. -/
private def dimacs (φ : CNF ℕ) (atomLines : List String) : String :=
  let vars := φ.foldl (fun m c => c.foldl (fun m l => max m (l.1 + 1)) m) atomLines.length
  let lit (l : Literal ℕ) : String := if l.2 then s!"{l.1 + 1}" else s!"-{l.1 + 1}"
  let clauses := φ.map fun c => " ".intercalate (c.map lit ++ ["0"])
  "\n".intercalate (atomLines ++ s!"p cnf {vars} {φ.length}" :: clauses)

/-- The checker's verdict on a certificate, evaluated by the kernel, for the error message after
the kernel did not accept it. -/
private def explainRejection (checkE cert : Expr) (ex : Exception) : MetaM MessageData := do
  match Kernel.whnf (← getEnv) {} checkE with
  | .ok r =>
    if r.isConstOf ``Bool.false then
      return m!"lrat_tauto: the LRAT checker rejected the certificate. It must refute the \
        numbered Plaisted–Greenbaum transformation of the negated goal, which `lrat_tauto?` \
        prints."
    return m!"lrat_tauto: the kernel could not evaluate the LRAT checker on the \
      certificate{indentExpr cert}\nIt must be a closed term whose definition the kernel can \
      unfold."
  | .error _ => return m!"lrat_tauto: the kernel did not accept the certificate:\n\
      {ex.toMessageData}"

initialize registerTraceClass `lrat_tauto

/-- An array literal, as `List.toArray` of a list, which the kernel reduces directly. -/
private def arrayLit (ty : Expr) (xs : List Expr) : Expr :=
  mkApp2 (mkConst ``List.toArray [0]) ty <| xs.foldr (mkApp3 (mkConst ``List.cons [0]) ty)
    (mkApp (mkConst ``List.nil [0]) ty)

/-- **The certificate generator** of `lrat_tauto` without `using`: a model or an LRAT certificate
for a formula. It is the CDCL solver `Cslib.Algorithms.Lean.CDCL.solveCompact`, run in the
elaborator. It is not trusted, since the kernel checks the certificate it returns. A replacement,
such as `Cslib.Algorithms.Lean.DPLL.solve`, must return on `φ` either `.sat σ` with `φ.eval σ`
true, or `.unsat cert` with `CNF.checkLRAT φ cert` true (RUP additions and deletions only); the
module docstring states this contract. -/
private def generateCert (φ : CNF ℕ) : Cslib.Algorithms.Lean.DPLL.Result :=
  Cslib.Algorithms.Lean.CDCL.solveCompact φ

/-- The steps of a certificate that the empty clause depends on, through the hints, in order;
deletions are dropped. The kernel checker accepts the result whenever it accepts the
certificate, since a deleted clause is never hinted again. Dropping the deletions measured faster
than keeping the solver's or deleting each clause after its last hint: the checker's trie does
not get shallower when clauses are deleted, and each deletion costs a step. -/
private def trimCert (cert : Array LRAT.IntAction) : Array LRAT.IntAction := Id.run do
  let mut needed : Std.HashSet ℕ := {}
  let mut kept : Array LRAT.IntAction := #[]
  -- The steps after the first empty clause are never checked.
  let stop := (cert.findIdx? fun | .addEmpty .. => true | _ => false).getD cert.size
  for a in (cert.extract 0 (stop + 1)).reverse do
    match a with
    | .addEmpty _ hints =>
      needed := hints.foldl (·.insert ·) needed
      kept := kept.push a
    | .addRup id _ hints =>
      if needed.contains id then
        needed := hints.foldl (·.insert ·) needed
        kept := kept.push a
    | .addRat .. => kept := kept.push a
    | .del _ => pure ()
  return kept.reverse

/-- Renumbers the clauses that a certificate adds as `n + 1, n + 2, …` in order, after the `n`
clauses of the formula, and its hints and deletions accordingly, so that the kernel checker's
trie stays shallow. A hint to a number the certificate has not added keeps that number. -/
private def renumberCert (n : ℕ) (cert : Array LRAT.IntAction) : Array LRAT.IntAction :=
  Id.run do
  let mut m : Std.HashMap ℕ ℕ := {}
  let mut next := n + 1
  let mut out : Array LRAT.IntAction := #[]
  for a in cert do
    match a with
    | .addRup id c hints =>
      out := out.push (.addRup next c (hints.map fun h => m.getD h h))
      m := m.insert id next
      next := next + 1
    | .addEmpty _ hints =>
      out := out.push (.addEmpty next (hints.map fun h => m.getD h h))
      next := next + 1
    | .del ids => out := out.push (.del (ids.map fun h => m.getD h h))
    | .addRat .. => out := out.push a
  return out

/-- A certificate as an expression, with its numbers as raw literals. -/
private def certToExpr (cert : Array LRAT.IntAction) : Expr :=
  let natE (n : ℕ) : Expr := mkRawNatLit n
  let intE (i : Int) : Expr := match i with
    | .ofNat n => mkApp (mkConst ``Int.ofNat) (natE n)
    | .negSucc n => mkApp (mkConst ``Int.negSucc) (natE n)
  let nats (xs : Array ℕ) : Expr := arrayLit (mkConst ``Nat) (xs.toList.map natE)
  let ints (xs : Array Int) : Expr := arrayLit (mkConst ``Int) (xs.toList.map intE)
  let clauseT := mkApp (mkConst ``Array [0]) (mkConst ``Int)
  let ctor (n : Name) := mkApp2 (mkConst n [0, 0]) clauseT (mkConst ``Nat)
  let action : LRAT.IntAction → Expr
    | .addEmpty id hints => mkApp2 (ctor ``LRAT.Action.addEmpty) (natE id) (nats hints)
    | .addRup id c hints => mkApp3 (ctor ``LRAT.Action.addRup) (natE id) (ints c) (nats hints)
    | .del ids => mkApp (ctor ``LRAT.Action.del) (nats ids)
    | .addRat id c (v, b) hints ratHints =>
      let pair (α β : Expr) (a b : Expr) := mkApp4 (mkConst ``Prod.mk [0, 0]) α β a b
      let natsT := mkApp (mkConst ``Array [0]) (mkConst ``Nat)
      let ratT := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) natsT
      mkApp5 (ctor ``LRAT.Action.addRat) (natE id) (ints c)
        (pair (mkConst ``Nat) (mkConst ``Bool) (natE v) (toExpr b)) (nats hints)
        (arrayLit ratT (ratHints.toList.map fun (i, hs) => pair (mkConst ``Nat) natsT (natE i)
          (nats hs)))
  arrayLit (mkApp2 (mkConst ``LRAT.Action [0, 0]) clauseT (mkConst ``Nat))
    (cert.toList.map action)

/-- The certificate for the numbered Plaisted–Greenbaum transformation `φ` of a negated formula,
from the generator (`generateCert`), trimmed when the trimmed one is accepted; or, if `φ` is
satisfiable, the assignment the generator found. -/
private def certFor (φ : CNF ℕ) : MetaM (Except (ℕ → Bool) (Array LRAT.IntAction)) := do
  let start ← IO.monoMsNow
  match ← IO.lazyPure fun _ => generateCert φ with
  | .unsat cert =>
    let trimmed := renumberCert φ.length (trimCert cert)
    let ok := CNF.checkLRATFast φ trimmed
    trace[lrat_tauto] "{φ.length} clauses; the solver's certificate has {cert.size} steps, \
      {trimmed.size} after trimming{if ok then "" else ", rejected, so it is not used"}; \
      {(← IO.monoMsNow) - start} ms"
    return .ok (if ok then trimmed else cert)
  | .sat σ => return .error σ

/-- The error for a formula that the assignment `σ` falsifies: the goal is false and the premises
true under `σ`, read on the atoms. -/
private def countermodel (f : Formula) (σ : ℕ → Bool) : MessageData :=
  let lines := f.atoms.toList.zipIdx.map fun (e, i) =>
    m!"\n  {e} := {if σ i then "True" else "False"}"
  let given := f.premises.filter (·.source != .rfl)
  let names := given.toList.map fun p => m!"{p.proof}"
  let noun :=
    if given.all (·.source == .hyp) then "hypotheses"
    else if given.all (·.source == .term) then "terms"
    else "hypotheses and terms"
  if given.isEmpty then
    m!"lrat_tauto: the goal is not a propositional tautology. It is false under this \
      assignment to its atoms, read as independent propositions:{MessageData.joinSep lines ""}"
  else
    m!"lrat_tauto: the goal does not follow propositionally from the {noun} \
      {MessageData.joinSep names ", "}. It is false, and the {noun} are true, under this \
      assignment to the atoms of the goal and the {noun}, read as independent \
      propositions:{MessageData.joinSep lines ""}"

/-- The formula `f` of the goal `g`, or one with fewer premises, and a certificate for it. The
generator refutes `f`; the premises with a clause among the certificate's hints
(`usedPremises`) are kept, the formula is read again from them alone, which numbers its atoms
afresh, and the generator refutes that formula. If it does not, `f` and its certificate are
returned. If `f` is satisfiable, the error shows the assignment. -/
private def solveFormula (g : MVarId) (f : Formula) :
    MetaM (Formula × Array LRAT.IntAction) := do
  match ← certFor f.cnf with
  | .error σ => throwError countermodel f σ
  | .ok cert =>
    let used := usedPremises f cert
    if used.all id then return (f, cert)
    let ps := (f.premises.zip used).filterMap fun (p, u) => if u then some p else none
    let core ← readFormula g ps false
    match ← certFor core.cnf with
    | .ok coreCert =>
      trace[lrat_tauto] "{ps.size} of the {f.premises.size} premises are used; the formula is \
        read again from them"
      return (core, coreCert)
    | .error _ =>
      trace[lrat_tauto] "the formula read from the {ps.size} premises used is satisfiable, so \
        all {f.premises.size} are kept"
      return (f, cert)

/-- The body of the valuation `valuation atoms`, for the atoms numbered `lo, …, hi - 1`: a
balanced tree of `cond (Nat.blt i.val m) …`, where `i : Fin n` is the bound variable `#0`. The
atoms have no loose bound variables, since `reify` only descends into non-dependent arrows. -/
private partial def valuationTree (atoms : Array Expr) (lo hi : ℕ) : Expr :=
  if hi ≤ lo then mkConst ``False
  else if hi = lo + 1 then atoms[lo]!
  else
    let m := (lo + hi) / 2
    let iv := mkApp2 (mkConst ``Fin.val) (toExpr atoms.size) (.bvar 0)
    mkApp4 (mkConst ``cond [1]) (mkSort .zero) (mkApp2 (mkConst ``Nat.blt) iv (mkRawNatLit m))
      (valuationTree atoms lo m) (valuationTree atoms m hi)

/-- The valuation `v : Fin n → Prop` sending the atom numbered `i` to the expression it was read
from, by a binary search on `i.val`: the kernel reaches each atom in about `log₂ n` comparisons
of numerals. A chain of `Matrix.vecCons` takes `i` steps of `Fin.cases` to reach the atom `i`;
on the chain of 320 implications, those lookups took almost all of the 6 seconds that the kernel
spent on the final step, against 0.3 seconds with this valuation. -/
private def valuation (atoms : Array Expr) : Expr :=
  .lam `i (toTypeExpr (Fin atoms.size)) (valuationTree atoms 0 atoms.size) .default

/-- Closes the goal `g`, already introduced, from the certificate `cert` for the goal with the
term premises `terms` alone, or from one the generator finds for the goal and the premises: with
`hyps`, the propositional hypotheses of the context, then `terms`, then the atoms `rfl` proves. -/
private def closeGoal (g : MVarId) (cert : Option Expr) (hyps : Bool) (terms : Array Premise) :
    MetaM Unit :=
  g.withContext do
  let (f, cert) ← match cert with
    | some cert => pure (← readFormula g terms false, cert)
    | none =>
      let f ← readFormula g ((← if hyps then contextPremises else pure #[]) ++ terms) true
      let (f, cert) ← solveFormula g f
      pure (f, certToExpr cert)
  let s := f.shape
  let atoms := f.atoms
  let n := atoms.size
  let a := propositionToExpr (s.toProposition n)
  let negA := mkApp3 (mkConst ``Proposition.imp [0]) (toTypeExpr (Fin n)) a
    (mkApp (mkConst ``Proposition.falsum [0]) (toTypeExpr (Fin n)))
  let φE ← mkAppM ``Proposition.plaistedGreenbaumNumberedCNF #[negA]
  let checkE ← mkAppM ``CNF.checkLRATKernel #[φE, cert]
  let checkProp ← mkEq checkE (mkConst ``Bool.true)
  let start ← IO.monoMsNow
  let hcheck ← try
      mkConst <$> withOptions (Elab.async.set · false)
        (mkAuxLemma [] checkProp (← mkDecideProof checkProp))
    catch ex => throwError (← explainRejection checkE cert ex)
  trace[lrat_tauto] "the kernel checked the certificate in {(← IO.monoMsNow) - start} ms"
  let v := valuation atoms
  -- `checkLRATKernel φ cert = true`, rewritten to `checkLRATRat φ cert = true`
  let hcheck ← mkEqTrans
    (← mkEqSymm (← mkAppM ``CNF.checkLRATKernel_eq_checkLRATRat #[φE, cert])) hcheck
  let hA ← mkAppM ``Proposition.eval_prop_of_checkLRATRat #[hcheck, v]
  let (_, p, hiff) ← s.iffGoal
  -- `hiff : X ↔ P`, where `X` is `A.eval v` up to unfolding `eval` and the valuation, and `P` is
  -- `P₁ → ⋯ → Pₖ → G` for the premises `Pᵢ`.
  g.assign <| mkAppN (mkApp4 (mkConst ``Iff.mp) (← inferType hA) p hiff hA)
    (f.premises.map (·.proof))

end

open Std.Tactic.BVDecide (LRAT.IntAction) in
elab_rules : tactic
  | `(tactic| lrat_tauto $cfg:optConfig $[[$ts,*]]? $[using $cert]?) => do
    let mut hyps := true
    for item in cfg.raw[0].getArgs do
      match item[0] with
      | `(Lean.Parser.Tactic.negConfigItem| -hyps) => hyps := false
      | `(Lean.Parser.Tactic.posConfigItem| +hyps) => hyps := true
      | _ => throwErrorAt item "lrat_tauto: unknown option; the only option is `-hyps`"
    let g ← introNonProps (← getMainGoal)
    replaceMainGoal [g]
    g.withContext do
      let certE ← cert.mapM fun cert => do
        let certE ← instantiateMVars
          (← elabTermEnsuringType cert (mkApp (mkConst ``Array [0]) (mkConst ``LRAT.IntAction)))
        if certE.hasFVar || certE.hasMVar then
          throwError "lrat_tauto: the certificate must be a closed term:{indentExpr certE}"
        return certE
      closeGoal g certE hyps (← termPremises ((ts.map (·.getElems)).getD #[]))
    replaceMainGoal []

elab_rules : tactic
  | `(tactic| lrat_tauto? $[[$ts,*]]?) => do
    let ts := (ts.map (·.getElems)).getD #[]
    let msg ← withoutModifyingState do
      let g ← introNonProps (← getMainGoal)
      replaceMainGoal [g]
      g.withContext do
        let f ← readFormula g (← termPremises ts) false
        let φ := f.cnf
        let atomLines ← f.atoms.toList.zipIdx.mapM fun (e, i) => do
          let shown := (← ppExpr e).pretty 1000000
          return s!"c {i + 1} := {shown.replace "\n" " "}"
        return dimacs φ atomLines
    let premises := if ts.isEmpty then m!"," else m!", with the terms as premises,"
    logInfo m!"The numbered Plaisted–Greenbaum transformation of the negated goal{premises} in \
      DIMACS form:\n{msg}"

end Cslib.Tactic.LRATTauto

end
