/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.CircuitBound.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public meta import Lean.Elab.Tactic.Simp

/-!
# Bounding a quantity by the structure of a term

`circuit_bound` proves a bound `m ≤ b` between natural numbers when `m` is determined by the
structure of a term: the depth, size or cost of a circuit built with combinators from named
pieces. It replaces the hand-written chain

```
apply (Circuit.depth_append_le _ _).trans
apply max_le
· apply Circuit.depth_pi_le
  intro i
  exact (Formula.depth_toCircuit_le _).trans (by simp [generateFormula])
· apply Circuit.depth_pi_le
  intro i
  exact (Formula.depth_toCircuit_le _).trans (by simp [propagateFormula])
```

by `circuit_bound [step, generateFormula, propagateFormula]`.

## How it works

The tactic computes an upper bound of `m` and leaves the comparison of that bound with `b` to
`omega`, falling back to splitting top-level `max`s and `nlinarith` / `grind` when the comparison is
polynomial rather than linear. It bounds sums, products, powers with a fixed exponent, maxima,
finite sums, mapped list sums, finite suprema and conditionals from bounds of their parts. At any
other term `t` it tries, in this order:

1. If `t` occurs in `b`, it keeps `t`.
2. A local hypothesis `t ≤ c` or `t = c`, possibly under quantifiers: an induction hypothesis, or a
   bound `∀ j, (cs j).depth ≤ D` of a family.
3. A theorem tagged `@[circuit_bound]` whose left-hand side matches `t`; it then bounds the
   right-hand side. The rules of the combinators and the bounds of named constructions are
   registered this way.
4. The simp set `circuit_simps` with the lemmas given in brackets, which unfolds the listed
   definitions and applies exact rules such as `Circuit.depth_wiring`; it then bounds the result.
5. Otherwise it keeps `t`.

The traversal knows nothing about circuits: the tagged theorems and the simp set are the only
circuit-specific parts, and they are attached in `CslibFrontier.Computability.Circuit.Simps`.

## When to use something else

* For an equation `m = b`, use `simp only [circuit_simps, …]` and `omega`: no bound has to be
  chosen.
* When the arithmetic after the structural bound is beyond `omega`, `nlinarith` and `grind` (for
  instance, higher-degree monotonicity or exponent arithmetic), state the structural bound as a
  `have` proved by `circuit_bound` and finish by hand, or rewrite with `grw [Circuit.depth_comp_le,
  h]` and continue with the goal it leaves.

## Main definitions

* `circuit_bound`: the tactic.

## Implementation notes

`dite_le_max`, `forall_mem_ofFn` and `sum_map_le_length_mul` are used in the proofs the tactic
builds, so they are public. The other monotonicity steps use `Nat.add_le_add`, `Nat.mul_le_mul`,
`Nat.pow_le_pow_left`, `max_le_max`, `ite_le_sup`, `Finset.sum_le_sum` and `Finset.sup_le`.
-/

public section

namespace Cslib.Tactic.CircuitBound

/-- A dependent conditional is at most the larger of the bounds of its branches. -/
theorem dite_le_max {p : Prop} [Decidable p] {a : p → ℕ} {b : ¬p → ℕ} {A B : ℕ}
    (ha : ∀ h, a h ≤ A) (hb : ∀ h, b h ≤ B) : dite p a b ≤ max A B := by
  split
  · exact (ha _).trans (le_max_left A B)
  · exact (hb _).trans (le_max_right A B)

/-- A predicate holding at every `f j` holds for every member of `List.ofFn f`. -/
theorem forall_mem_ofFn {α : Type*} {n : ℕ} {f : Fin n → α} {P : α → Prop}
    (h : ∀ j, P (f j)) : ∀ a ∈ List.ofFn f, P a := by
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
  exact h j

/-- The sum of `l.map f` is at most `l.length * B` when every member of `l` satisfies `f a ≤ B`. -/
theorem sum_map_le_length_mul {α : Type*} {l : List α} {f : α → ℕ} {B : ℕ}
    (h : ∀ a ∈ l, f a ≤ B) : (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have ha := h a List.mem_cons_self
    have hl := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    omega

end Cslib.Tactic.CircuitBound

end

public meta section

namespace Cslib.Tactic.CircuitBound

open Lean Meta Elab Tactic

/-- What the traversal reads. -/
private structure Context where
  /-- The simp set `circuit_simps` with the lemmas given to the tactic. -/
  simpCtx : Simp.Context
  /-- The simplification procedures of that simp call. -/
  simprocs : Simp.SimprocsArray
  /-- The right-hand side of the goal: its subterms are not bounded. -/
  target : Expr

/-- What the traversal could not bound, for the error message. -/
private structure State where
  /-- Terms with a registered bound for their head symbol, none of which applied, with their
  display in the context where they were met. -/
  unbounded : Array (Expr × MessageData) := #[]
  /-- Families whose bound depends on the index. -/
  notes : Array MessageData := #[]

/-- The monad of the traversal. -/
private abbrev BoundM := ReaderT Context <| StateRefT State MetaM

/-- An upper bound `val` of a number, with a proof that is absent when `val` is the number. -/
private structure Bound where
  /-- The bound. -/
  val : Expr
  /-- The proof that the number is at most `val`. -/
  proof? : Option Expr

/-- The proposition `a ≤ b` between natural numbers. -/
private def natLE (a b : Expr) : Expr :=
  mkApp4 (mkConst ``LE.le [Level.zero]) (mkConst ``Nat) (mkConst ``instLENat) a b

/-- The instance of the class `cls` on the natural numbers. -/
private def natInst (cls : Name) : MetaM Expr :=
  synthInstance (mkApp (mkConst cls [Level.zero]) (mkConst ``Nat))

/-- The proof of a bound. -/
private def Bound.proof (b : Bound) : Expr :=
  b.proof?.getD (mkApp (mkConst ``Nat.le_refl) b.val)

/-- The bound that `proof` proves. -/
private def Bound.ofProof (proof : Expr) : MetaM Bound := do
  let type ← instantiateMVars (← inferType proof)
  let some (_, val, _) := boundSides? type
    | throwError "circuit_bound: not a bound{indentExpr type}"
  return ⟨val, proof⟩

/-- The bound `b` of `e'`, as a bound of `e`, given a proof `eq? : e = e'` or that the two are
definitionally equal. -/
private def Bound.ofEq (e : Expr) (eq? : Option Expr) (b : Bound) : MetaM Bound := do
  match eq? with
  | some eq => return ⟨b.val, ← mkAppM ``Nat.le_trans #[← mkAppM ``Nat.le_of_eq #[eq], b.proof]⟩
  | none => return ⟨b.val, ← mkExpectedTypeHint b.proof (natLE e b.val)⟩

/-- Run `x`, undoing its effects other than its notes if it fails. -/
private def attempt {α : Type} (x : BoundM α) : BoundM (Option α) := do
  let saved ← (saveState : MetaM Meta.SavedState)
  let state ← get
  try
    some <$> x
  catch _ =>
    saved.restore
    modify fun s => { state with notes := s.notes }
    return none

/-- Fail, with a note, if the bound `val` of `e` mentions one of the variables `xs`. -/
private def checkUniform (xs : Array Expr) (e val : Expr) : BoundM Unit := do
  if xs.any fun x => val.containsFVar x.fvarId! then
    let vars := MessageData.joinSep (xs.toList.map fun x => m!"`{x}`") ", "
    let found := if val == e then m!"No bound of{indentExpr e}\nis known that does not depend on \
      {vars}." else m!"The bound{indentExpr val}\nof{indentExpr e}\ndepends on {vars}."
    let note ← addMessageContext m!"{found} State a bound of the family as a hypothesis \
      `∀ j, … ≤ D`."
    modify fun s => { s with notes := s.notes.push note }
    throwError "the bound depends on a bound variable"

mutual

/-- Bound the natural number `e` from above, following its structure. -/
private partial def bound (e : Expr) : BoundM Bound := do
  let e ← instantiateMVars e
  match_expr e with
  | HAdd.hAdd α _ _ _ a b =>
    if α.isConstOf ``Nat then combine ``Nat.add_le_add e a b else boundTerm e
  | HMul.hMul α _ _ _ a b =>
    if α.isConstOf ``Nat then combine ``Nat.mul_le_mul e a b else boundTerm e
  | HPow.hPow α β γ _ a b =>
    if α.isConstOf ``Nat && β.isConstOf ``Nat && γ.isConstOf ``Nat then
      let A ← bound a
      if A.proof?.isNone then boundTerm e
      else Bound.ofProof (← mkAppM ``Nat.pow_le_pow_left #[A.proof, b])
    else boundTerm e
  | Max.max _ _ a b =>
    let A ← bound a
    let B ← bound b
    if A.proof?.isNone && B.proof?.isNone then return ⟨e, none⟩
    let val := mkApp2 e.appFn!.appFn! A.val B.val
    let proof ← mkAppOptM ``max_le_max
      #[mkConst ``Nat, ← natInst ``LinearOrder, a, b, A.val, B.val, A.proof, B.proof]
    return ⟨val, some (← mkExpectedTypeHint proof (natLE e val))⟩
  | ite _ p inst a b =>
    -- a conditional is at most the maximum of its branches
    let m ← mkAppM ``Max.max #[a, b]
    let proof ← mkAppOptM ``ite_le_sup #[mkConst ``Nat, ← natInst ``SemilatticeSup, a, b, p, inst]
    let proof ← mkExpectedTypeHint proof (natLE e m)
    let B ← bound m
    return ⟨B.val, some (← mkAppM ``Nat.le_trans #[proof, B.proof])⟩
  | dite _ p inst a b =>
    let branches ← attempt do
      let (A, hA) ← boundUnder `h p fun h => a.beta #[h]
      let (B, hB) ← boundUnder `h (mkNot p) fun h => b.beta #[h]
      mkAppOptM ``dite_le_max #[p, inst, a, b, A, B, hA, hB]
    match branches with
    | some proof => Bound.ofProof proof
    | none => boundTerm e
  | Finset.sum ι _ _ s f =>
    withLocalDeclD `j ι fun j => do
      let b ← bound (f.beta #[j])
      if b.proof?.isNone then return ⟨e, none⟩
      let g ← mkLambdaFVars #[j] b.val
      let val := mkApp2 e.appFn!.appFn! s g
      let h ← withLocalDeclD `hj (← mkAppM ``Membership.mem #[s, j]) fun hj =>
        mkLambdaFVars #[j, hj] b.proof
      let proof ← mkAppOptM ``Finset.sum_le_sum #[ι, mkConst ``Nat, ← natInst ``AddCommMonoid,
        ← natInst ``Preorder, f, g, s, none, h]
      return ⟨val, some (← mkExpectedTypeHint proof (natLE e val))⟩
  | Finset.sup α ι instSup instBot s f =>
    let b ← boundTerm e
    if b.proof?.isSome || !α.isConstOf ``Nat || e.occurs (← read).target then return b
    let supBound ← attempt do
      let (val, h) ← boundUnder `j ι fun j => f.beta #[j]
      let hmem ← withLocalDeclD `j ι fun j => do
        withLocalDeclD `hj (← mkAppM ``Membership.mem #[s, j]) fun hj =>
          mkLambdaFVars #[j, hj] (h.beta #[j])
      let proof ← mkAppOptM ``Finset.sup_le #[α, ι, instSup, instBot, s, f, val, hmem]
      return (val, ← mkExpectedTypeHint proof (natLE e val))
    return match supBound with
      | some (val, proof) => ⟨val, some proof⟩
      | none => b
  | List.sum α _ _ xs =>
    let b ← boundTerm e
    if b.proof?.isSome || !α.isConstOf ``Nat || e.occurs (← read).target then return b
    let_expr List.map β _ f l := xs | return b
    let listBound ← attempt do
      withLocalDeclD `a β fun a => do
        withLocalDeclD `ha (← mkAppM ``Membership.mem #[l, a]) fun ha => do
          let e' := f.beta #[a]
          let ba ← bound e'
          if ba.val.containsFVar ha.fvarId! then throwError "depends on membership proof"
          checkUniform #[a] e' ba.val
          let h ← mkLambdaFVars #[a, ha] ba.proof
          Bound.ofProof (← mkAppOptM ``sum_map_le_length_mul #[β, l, f, ba.val, h])
    return listBound.getD b
  | _ => boundTerm e

/-- Bound an operation by the same operation on bounds of its arguments `a` and `b`, by the
monotonicity lemma `rule`. -/
private partial def combine (rule : Name) (e a b : Expr) : BoundM Bound := do
  let A ← bound a
  let B ← bound b
  if A.proof?.isNone && B.proof?.isNone then return ⟨e, none⟩
  Bound.ofProof (← mkAppM rule #[A.proof, B.proof])

/-- A bound of `body x` that does not depend on `x : type`, proved for all `x`. -/
private partial def boundUnder (n : Name) (type : Expr) (body : Expr → Expr) :
    BoundM (Expr × Expr) :=
  withLocalDeclD n type fun x => do
    let e := body x
    let b ← bound e
    checkUniform #[x] e b.val
    return (b.val, ← mkLambdaFVars #[x] b.proof)

/-- Bound a term that is not an arithmetic expression: by a local hypothesis, by a registered
bound, by normalizing it with the simp set, or by itself. -/
private partial def boundTerm (e : Expr) : BoundM Bound := do
  unless e.isApp do return ⟨e, none⟩
  if e.isAppOf ``OfNat.ofNat || e.occurs (← read).target then return ⟨e, none⟩
  if let some b ← pushConditional? e then return b
  for decl in (← getLCtx).decls.toArray.reverse.filterMap id do
    if decl.isImplementationDetail then continue
    unless (boundSides? (← instantiateMVars decl.type).getForallBody).isSome do continue
    if let some (rhs, proof) ← attempt (applyBound decl.toExpr e) then
      trace[circuit_bound] "{decl.toExpr}: {e} ≤ {rhs}"
      return ⟨rhs, some proof⟩
  let bounds := boundExt.getState (← getEnv)
  for rule in (← bounds.getMatch e).reverse do
    if let some (rhs, proof) ← attempt (do applyBound (← mkConstWithFreshMVarLevels rule) e) then
      trace[circuit_bound] "{.ofConstName rule}: {e} ≤ {rhs}"
      let b ← bound rhs
      if b.proof?.isNone then return ⟨rhs, some proof⟩
      return ⟨b.val, some (← mkAppM ``Nat.le_trans #[proof, b.proof])⟩
  let (r, _) ← simp e (← read).simpCtx (← read).simprocs
  if r.expr != e then return ← Bound.ofEq e r.proof? (← bound r.expr)
  if let .const f _ := e.getAppFn then
    if bounds.root.contains (.const f e.getAppNumArgs) then
      unless (← get).unbounded.any (·.1 == e) do
        let shown ← addMessageContext m!"{e}"
        modify fun s => { s with unbounded := s.unbounded.push (e, shown) }
  return ⟨e, none⟩

/-- Move the function applied to a conditional into its branches, and bound the result. -/
private partial def pushConditional? (e : Expr) : BoundM (Option Bound) := do
  let f := e.getAppFn
  let args := e.getAppArgs
  for i in [0:args.size] do
    let apply (z : Expr) := mkAppN f (args.set! i z)
    let some (e', eq) ← (do
      match_expr args[i]! with
      | ite α p inst x y =>
        let motive ← withLocalDeclD `c α fun c => mkLambdaFVars #[c] (apply c)
        unless ← isTypeCorrect motive do return none
        let e' ← mkAppOptM ``ite #[mkConst ``Nat, p, inst, apply x, apply y]
        return some (e', ← mkAppOptM ``apply_ite #[none, none, motive, p, inst, x, y])
      | dite α p inst x y =>
        let motive ← withLocalDeclD `c α fun c => mkLambdaFVars #[c] (apply c)
        unless ← isTypeCorrect motive do return none
        let branch (q z : Expr) := withLocalDeclD `h q fun h =>
          mkLambdaFVars #[h] (apply (z.beta #[h]))
        let e' ← mkAppOptM ``dite #[mkConst ``Nat, p, inst, ← branch p x, ← branch (mkNot p) y]
        return some (e', ← mkAppOptM ``apply_dite #[none, none, motive, p, inst, x, y])
      | _ => return none : BoundM (Option (Expr × Expr))) | continue
    return some (← Bound.ofEq e (← mkExpectedTypeHint eq (← mkEq e e')) (← bound e'))
  return none

/-- Use `proof` of `∀ xs, lhs ≤ rhs` or `∀ xs, lhs = rhs` on `e` if `lhs` matches it. A hypothesis
`∀ j, m j ≤ ?D` or `∀ x ∈ List.ofFn f, m x ≤ ?D` whose bound `?D` the match leaves open is proved
by bounding `m` uniformly in the index; any other hypothesis must be a local hypothesis. Returns
`rhs` and a proof of `e ≤ rhs`. -/
private partial def applyBound (proof e : Expr) : BoundM (Expr × Expr) := do
  let (xs, binders, body) ← forallMetaTelescope (← instantiateMVars (← inferType proof))
  let some (lhs, rhs, isEq) := boundSides? body | throwError "not a bound"
  unless ← withReducibleAndInstances (isDefEq lhs e) do throwError "no match"
  for x in xs, binder in binders do
    let goal := x.mvarId!
    if ← goal.isAssigned then continue
    let type ← instantiateMVars (← goal.getType)
    if binder.isInstImplicit then
      goal.assign (← synthInstance type)
    else if ← isProp type then
      let uniform ← forallTelescope type fun js body => do
        let some (lhs, rhs, false) := boundSides? body | return false
        unless rhs.isMVar do return false
        -- `∀ a ∈ List.ofFn f, m a ≤ ?D`: substitute `a := f j` and bound uniformly in `j`.
        if js.size == 2 then
          let a := js[0]!
          let ha := js[1]!
          let haType ← instantiateMVars (← inferType ha)
          if let some (_, _, _, list, elem) :=
              (match_expr haType with
              | Membership.mem α γ inst list elem => some (α, γ, inst, list, elem)
              | _ => none) then
            if elem == a then
              let list ← instantiateMVars list
              if let some (_, n, f) :=
                  (match_expr list with
                  | List.ofFn α n f => some (α, n, f)
                  | _ => none) then
                let (val, hfin) ← withLocalDeclD `j (mkApp (mkConst ``Fin) n) fun j => do
                  let lhs' := lhs.replaceFVar a (f.beta #[j])
                  let b ← bound lhs'
                  checkUniform #[j] lhs' b.val
                  return (b.val, ← mkLambdaFVars #[j] b.proof)
                rhs.mvarId!.assign val
                let P ← mkLambdaFVars #[a] (natLE lhs val)
                goal.assign (← mkAppOptM ``forall_mem_ofFn #[none, n, f, P, hfin])
                return true
        let b ← bound lhs
        checkUniform js lhs b.val
        rhs.mvarId!.assign b.val
        goal.assign (← mkLambdaFVars js b.proof)
        return true
      unless uniform do goal.assumption
  let proof ← instantiateMVars (mkAppN proof xs)
  let rhs ← instantiateMVars rhs
  if proof.hasExprMVar || rhs.hasExprMVar then throwError "undetermined arguments"
  return (rhs, ← if isEq then mkAppM ``Nat.le_of_eq #[proof] else pure proof)

end

/-- `circuit_bound` proves a goal `m ≤ b` between natural numbers by bounding `m` along the
structure of the term it measures, typically the depth, size or cost of a circuit, and comparing
the bound with `b` by `omega` (falling back to splitting top-level `max`s and `nlinarith` / `grind`
for polynomial comparisons).

* `circuit_bound [step, generateFormula]` also unfolds the definitions `step` and
  `generateFormula` and uses any other simp lemma in the list; the simp set `circuit_simps` is
  always used.
* A named sub-circuit is bounded by a theorem tagged `@[circuit_bound]`, such as
  `(adder w).depth ≤ 6`, or by a local hypothesis, such as an induction hypothesis. Without either
  its measure stays in the bound, which suits a goal `(wrap M).depth ≤ M.depth + 1`.
* A family, as in `Circuit.pi fun j => cs j` or `List.ofFn fun j => cs j`, needs a bound that does
  not depend on `j`. The tactic finds it when every `cs j` has the same structural bound, also
  through `if … then … else`. Otherwise state it first: `have h : ∀ j, (cs j).depth ≤ D := …`.

When it fails, the error shows the comparison `omega`/`nlinarith`/`grind` could not prove, the
sub-terms for which a bound was expected but none is registered or assumed, and the families whose
bound depends on the index. `set_option trace.circuit_bound true` shows the bounds it used.

Use `grw [Circuit.depth_comp_le, h]` instead when one step is wanted inside a larger inequality,
when the goal is not of the form `m ≤ b`, or when the arithmetic that remains is beyond `omega`,
`nlinarith` and `grind`; a structural bound stated as a `have` and proved by `circuit_bound` also
serves the last case. For an equation `m = b` use `simp only [circuit_simps, …]`. -/
syntax (name := circuitBound) "circuit_bound" (" [" Parser.Tactic.simpLemma,* "]")? : tactic

/-- Elaborate `circuit_bound`: bound the left-hand side, then compare with `omega` (falling back to
splitting top-level `max`s and `nlinarith` / `grind`). -/
@[tactic circuitBound] def evalCircuitBound : Tactic := fun stx => do
  let args : Syntax.TSepArray ``Parser.Tactic.simpLemma "," := ⟨stx[1][1].getArgs⟩
  let simpStx ← `(tactic| simp only [circuit_simps, $args,*])
  withMainContext do
  let { ctx, simprocs, .. } ← mkSimpContext simpStx (eraseLocal := false)
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (lhs, rhs, false) := boundSides? target
    | throwError "circuit_bound expects a goal `m ≤ b` between natural numbers, got\
        {indentExpr target}"
  let (b, state) ← ((bound lhs).run { simpCtx := ctx, simprocs, target := rhs }).run {}
  let rest ← mkFreshExprSyntheticOpaqueMVar (natLE b.val rhs)
  goal.assign (← mkAppM ``Nat.le_trans #[b.proof, rest])
  let (rest?, _) ← simpTarget rest.mvarId! ctx simprocs
  let some rest := rest? | replaceMainGoal []
  -- Close only `rest` so any other open goals stay untouched.
  replaceMainGoal [rest]
  try
    evalTactic (← `(tactic| omega))
  catch _ =>
    let saved ← saveState
    try
      let remaining ← evalTacticAt (← `(tactic|
        (repeat apply max_le) <;> (first | omega | nlinarith | grind))) rest
      unless remaining.isEmpty do throwError "unsolved goals"
      replaceMainGoal []
    catch _ =>
      saved.restore
      let mut msg := m!"circuit_bound could not prove{indentExpr (← rest.getType)}"
      unless state.unbounded.isEmpty do
        msg := msg ++ m!"\nNo bound is registered or assumed for{indentD (MessageData.joinSep
          (state.unbounded.toList.map (·.2)) Format.line)}"
      for note in state.notes do
        msg := msg ++ m!"\n{note}"
      throwError msg

end Cslib.Tactic.CircuitBound
