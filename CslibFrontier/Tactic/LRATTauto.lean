/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.TseitinCNF.Refutation
public import Mathlib.Data.Fin.VecNotation
public meta import CslibFrontier.Logics.Propositional.TseitinCNF.Numbered
public meta import Mathlib.Util.AtomM
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# Propositional tautologies over `Prop` from LRAT certificates

`lrat_tauto using cert` proves a goal built from `∧`, `∨`, `→`, `¬`, `↔`, `True` and `False` over
arbitrary propositions, the *atoms*, from an LRAT certificate `cert : Array LRAT.IntAction`. The
kernel checks the certificate; the proof uses no native evaluation, and its axioms are those of
`Cslib.Logic.PL.Proposition.eval_prop_of_checkLRAT`.

The tactic reads the goal `P` as a proposition `A : Proposition (Fin n)` and a valuation
`v : Fin n → Prop` of its atoms, with `A.eval v ↔ P`. It then applies
`Cslib.Logic.PL.Proposition.eval_prop_of_checkLRAT` to `A` and `v`: its hypothesis, that
`Cslib.Logic.PL.CNF.checkLRAT` accepts `cert` on `(imp A falsum).tseitinNumberedCNF`, is proved by
`decide`, so the kernel runs the checker. Only that run is trusted; where the certificate came
from does not matter. The goals proved are the classical tautologies, since
`eval_prop_of_checkLRAT` decides each atom classically.

## Reading the goal

* Leading binders whose type is not a proposition, as in `∀ (p q : Prop) (n : ℕ), …`, are
  introduced first. Hypotheses in the local context are not used: revert the ones the proof
  needs.
* `P ∧ Q`, `P ∨ Q`, `False` and an implication `P → Q` between propositions (a non-dependent
  arrow whose domain is a proposition) are read as the constructors `and`, `or`, `falsum` and
  `imp`. `Proposition` has no other constructors, so the other connectives are encoded:
  `¬P` as `imp P falsum`, `True` as `imp falsum falsum`, and `P ↔ Q` as
  `and (imp P Q) (imp Q P)`.
* Every other subterm is an atom: an equation `f x = y`, an order fact `n < 3`, a dependent `∀`
  or `∃`, a definition such as `a ≠ b` that unfolds to a connective. Atoms are numbered from `0`
  in order of first occurrence, left to right, and two atoms are the same when they are
  definitionally equal at reducible transparency.

## The certificate

The certificate refutes the numbered Tseitin transformation of `imp A falsum`, in which the atom
numbered `i` is the DIMACS variable `i + 1` and the clauses are numbered `1, 2, …` in order.
`lrat_tauto?` prints that formula in DIMACS form, with the atoms in comment lines, so that a SAT
solver producing LRAT proofs can refute it. The lines of a textual LRAT proof are the `addRup`,
`addEmpty` and `del` actions of the certificate; the checker rejects RAT steps, which some solvers
emit after preprocessing (CaDiCaL does not with `--plain`).

The kernel checks the certificate once, as an auxiliary lemma that the proof then cites. If it
fails, `lrat_tauto` evaluates the checker in the kernel to tell a rejected certificate from one
the kernel cannot evaluate, such as a definition from another module whose body is not exposed,
and reports which.

## Main definitions

* `lrat_tauto using cert`: close the goal from the certificate `cert`.
* `lrat_tauto?`: print the formula that a certificate for the goal must refute.

## Limitations

* `↔` is encoded by writing each side twice, so a goal that nests `↔` to depth `d` has up to
  `2 ^ d` copies of its innermost subformulas.
* The kernel evaluates a checker on lists, which is slow. On the pigeonhole formulas for five
  pigeons in four holes (193 steps) and six in five (395 steps), elaborating the certificate and
  checking it took about 3 and 13 seconds.
* Certificates are not generated here: they come from the user.
-/

public section

namespace Cslib.Tactic.LRATTauto

open Lean Meta Elab Tactic Mathlib.Tactic
open Cslib.Logic.PL

/-- `lrat_tauto using cert` closes a goal built from `∧`, `∨`, `→`, `¬`, `↔`, `True` and `False`
over arbitrary propositions, from an LRAT certificate `cert : Array LRAT.IntAction` that refutes
the numbered Tseitin transformation of the negated goal. The kernel checks the certificate by
evaluating `Cslib.Logic.PL.CNF.checkLRAT`. Leading binders over non-propositions, such as
`∀ p q : Prop`, are introduced first; hypotheses in the context are not used. The atoms are the
maximal subterms that are not connectives, compared at reducible transparency.

The certificate is a closed term the kernel can evaluate: a literal, or a definition whose body
it can unfold. A certificate the checker rejects is reported as such.

`lrat_tauto?` prints the formula the certificate must refute, in DIMACS form. -/
syntax (name := lratTauto) "lrat_tauto" " using " term : tactic

/-- `lrat_tauto?` prints the formula that a certificate for `lrat_tauto using` must refute: the
numbered Tseitin transformation of the negated goal in DIMACS form, preceded by comment lines
naming the variable of each atom. It leaves the goal unchanged. -/
syntax (name := lratTautoQuery) "lrat_tauto?" : tactic

/- `lrat_tauto?` only prints, so the unused tactic linter would flag every use. -/
allow_unused_tactic Cslib.Tactic.LRATTauto.lratTautoQuery

meta section

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

/-- Reads a proposition as a formula over its atoms. -/
private partial def reify (e : Expr) : AtomM Shape := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``False, #[]) => return .falsum
  | (``True, #[]) => return .verum
  | (``And, #[a, b]) => return .and (← reify a) (← reify b)
  | (``Or, #[a, b]) => return .or (← reify a) (← reify b)
  | (``Not, #[a]) => return .not (← reify a)
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

/-- The goal read as a formula, and its atoms. -/
private def readGoal (g : MVarId) : MetaM (Shape × Array Expr) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless ← isProp t do
    throwError "lrat_tauto: the goal is not a proposition:{indentExpr t}"
  AtomM.run .reducible do
    let s ← reify t
    return (s, (← get).atoms)

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
        numbered Tseitin transformation of the negated goal, which `lrat_tauto?` prints."
    return m!"lrat_tauto: the kernel could not evaluate the LRAT checker on the \
      certificate{indentExpr cert}\nIt must be a closed term whose definition the kernel can \
      unfold."
  | .error _ => return m!"lrat_tauto: the kernel did not accept the certificate:\n\
      {ex.toMessageData}"

/-- Closes the goal `g`, already introduced, from the certificate `cert`. -/
private def closeGoal (g : MVarId) (cert : Expr) : MetaM Unit := g.withContext do
  let (s, atoms) ← readGoal g
  let n := atoms.size
  let a := propositionToExpr (s.toProposition n)
  let negA := mkApp3 (mkConst ``Proposition.imp [0]) (toTypeExpr (Fin n)) a
    (mkApp (mkConst ``Proposition.falsum [0]) (toTypeExpr (Fin n)))
  let checkE ← mkAppM ``CNF.checkLRAT #[← mkAppM ``Proposition.tseitinNumberedCNF #[negA], cert]
  let checkProp ← mkEq checkE (mkConst ``Bool.true)
  let hcheck ← try
      mkConst <$> withOptions (Elab.async.set · false)
        (mkAuxLemma [] checkProp (← mkDecideProof checkProp))
    catch ex => throwError (← explainRejection checkE cert ex)
  let v ← atoms.foldrM (fun e t => mkAppM ``Matrix.vecCons #[e, t])
    (← mkAppOptM ``Matrix.vecEmpty #[mkSort .zero])
  let hA ← mkAppM ``Proposition.eval_prop_of_checkLRAT #[hcheck, v]
  let (_, p, hiff) ← s.iffGoal
  -- `hiff : X ↔ P`, where `X` is `A.eval v` up to unfolding `eval` and the valuation.
  g.assign (mkApp4 (mkConst ``Iff.mp) (← inferType hA) p hiff hA)

end

open Std.Tactic.BVDecide (LRAT.IntAction) in
elab_rules : tactic
  | `(tactic| lrat_tauto using $cert) => do
    let g ← introNonProps (← getMainGoal)
    replaceMainGoal [g]
    g.withContext do
      let certE ← instantiateMVars
        (← elabTermEnsuringType cert (mkApp (mkConst ``Array [0]) (mkConst ``LRAT.IntAction)))
      if certE.hasFVar || certE.hasMVar then
        throwError "lrat_tauto: the certificate must be a closed term:{indentExpr certE}"
      closeGoal g certE
    replaceMainGoal []

elab_rules : tactic
  | `(tactic| lrat_tauto?) => do
    let msg ← withoutModifyingState do
      let g ← introNonProps (← getMainGoal)
      g.withContext do
        let (s, atoms) ← readGoal g
        let n := atoms.size
        let φ := (Proposition.imp (s.toProposition n) .falsum).tseitinNumberedCNF
        let atomLines ← atoms.toList.zipIdx.mapM fun (e, i) => do
          let shown := (← ppExpr e).pretty 1000000
          return s!"c {i + 1} := {shown.replace "\n" " "}"
        return dimacs φ atomLines
    logInfo m!"The numbered Tseitin transformation of the negated goal, in DIMACS form:\n{msg}"

end Cslib.Tactic.LRATTauto

end
