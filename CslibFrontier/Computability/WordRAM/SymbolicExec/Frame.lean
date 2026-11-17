/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Register facts across calls

A proof about a word-RAM program that calls subprograms carries the registers it still needs across
each call: the specification of a call gives its result state `y` and a *frame*, a statement
`∀ i, i ≠ r → … → y.regs i = x.regs i` of the registers the call leaves alone, and the proof needs
`y.regs a = v` for every register `a` the next call reads. Written by hand, each such fact names the
frames it passes, proves each of their premises at `a`, and names the hypothesis that gives the
value: `(cf _ (by decide) (by decide)).trans ((bf _ (by decide)).trans ha)`.

`regs_frame` proves these facts from the hypotheses, without naming them.

## Main definitions

* `regs_frame`: the tactic. It proves an equation between register reads and values, a
  conjunction or `Prop`-valued structure of such equations, or a frame, by following each read
  `y.regs a` back through the frames among the hypotheses to a hypothesis that states the value.

## Implementation notes

The tactic collects from the local context the *values* `h : s.regs a = v`, also as components of
a hypothesis that is a conjunction or a `Prop`-valued structure, and the *frames*: hypotheses
`∀ xs, s'.regs i = s.regs i`, and for an execution hypothesis `he : ExecWithin w c x y T`, or any
other `he : J …` with a lemma `J.regs_eq`, the frame `fun i hi => he.regs_eq hi` of the registers
the code `c` does not write. It then rewrites every read in the goal: a read with a value becomes
the value; a read of `x.set r v` or `x.write a v` is reduced (`WP.Exec.reduceRegsStep`); a read of
a state with a frame whose premises hold at the register becomes the read of the earlier state; a
read of a state introduced by `let` becomes the read of its definition. The premises of a frame are
proved by evaluation when they have no free variables, in the kernel for `c.Preserves a` and after
unfolding a predicate introduced by `let`, and otherwise by a hypothesis. The goal is proved when
both sides of the equation agree.
-/

public section

namespace Cslib.WordRAM

namespace RegsFrame

open Lean Meta Elab Tactic

/-- A register frame: a proof of a statement `∀ xs, s'.regs i = s.regs i` with `i` among `xs`. -/
private meta structure Frame where
  /-- The proof. -/
  proof : Expr
  /-- Its statement. -/
  type : Expr
  /-- How error messages name the frame. -/
  name : MessageData

/-- The facts about registers among the hypotheses. -/
private meta structure Facts where
  /-- The frames, by their later state `s'`. -/
  frames : Std.HashMap Expr (Array Frame) := {}
  /-- The values: `(s, a) ↦ (v, h)` for `h : s.regs a = v`. -/
  values : Std.HashMap (Expr × Expr) (Expr × Expr) := {}

/-- The parts `(r, s, i)` of a read `s.regs i` of a register of `s : Data r`. -/
private meta def read? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``Data.regs 3 then some (e.getArg! 0, e.getArg! 1, e.getArg! 2) else none

/-- The key of the register name `i : Fin r`: its value if it evaluates to a literal, so that
`Reg.levels` and `(3 : Fin 64)` are the same register, and otherwise the name itself. -/
private meta def regKey (r i : Expr) : MetaM Expr := do
  match ← WP.Exec.regValue? r i with
  | some k => return mkRawNatLit k
  | none => instantiateMVars i

/-- The frame `J.regs_eq he` of an execution hypothesis `he : J …`, such as `ExecWithin w c x y T`,
when the lemma `J.regs_eq` exists: `∀ i, c.Preserves i → y.regs i = x.regs i`. -/
private meta def execFrame? (he ty : Expr) (J : Name) : MetaM (Option Frame) := do
  let lemmaName := J ++ `regs_eq
  unless (← getEnv).contains lemmaName do return none
  withNewMCtxDepth do
    let c ← mkConstWithFreshMVarLevels lemmaName
    let (xs, bis, _) ← forallMetaTelescope (← inferType c)
    let some idx := bis.findIdx? (· == .default) | return none
    unless ← isDefEq (← inferType xs[idx]!) ty do return none
    unless ← isDefEq xs[idx]! he do return none
    let proof := (← abstractMVars (mkAppN c xs) (levels := false)).expr
    if proof.hasMVar then return none
    return some { proof, type := ← inferType proof, name := m!"{he}.regs_eq" }

/-- Whether `ty` states a frame, `∀ xs, s'.regs i = s.regs i` with `i` among `xs` and the later
state `s'` not depending on `xs`; returns `s'`. -/
private meta def frameState? (ty : Expr) : Option Expr := do
  guard ty.isForall
  let (_, lhs, rhs) ← ty.getForallBody.eq?
  let (_, s', i) ← read? lhs
  let (_, _, i') ← read? rhs
  guard (i.isBVar && i == i' && !s'.hasLooseBVars)
  return s'

/-- Record the fact `h : ty`: a value, a frame, an execution, or a conjunction or `Prop`-valued
structure, whose components are recorded in turn. -/
private meta partial def addFact (h ty : Expr) (depth : ℕ := 0) : StateT Facts MetaM Unit := do
  let ty := ty.cleanupAnnotations
  let addFrame (f : Frame) (s' : Expr) : StateT Facts MetaM Unit :=
    modify fun F => { F with frames := F.frames.insert s' ((F.frames.getD s' #[]).push f) }
  if let some (_, lhs, rhs) := ty.eq? then
    let some (r, s, i) := read? lhs | return
    if (rhs.find? (· == lhs)).isSome then return
    let key := (s, ← regKey r i)
    -- A value is not replaced by an equation between two reads of the register.
    if (read? rhs).isSome && (← get).values.contains key then return
    modify fun F => { F with values := F.values.insert key (rhs, h) }
  else if let some s' := frameState? ty then
    addFrame { proof := h, type := ty, name := m!"{h}" } s'
  else if ty.isForall then
    return
  else if let some (p, q) := ty.and? then
    addFact (mkApp3 (mkConst ``And.left) p q h) p depth
    addFact (mkApp3 (mkConst ``And.right) p q h) q depth
  else
    let .const c _ := ty.getAppFn | return
    if let some f ← execFrame? h ty c then
      if let some s' := frameState? f.type then addFrame f s'
      return
    let env ← getEnv
    unless depth < 3 && isStructure env c do return
    let some info := env.find? c | return
    unless info.type.getForallBody.isProp do return
    for field in getStructureFields env c do
      let some proj := getProjFnForField? env c field | continue
      let p ← mkAppOptM proj ((ty.getAppArgs.map some).push (some h))
      addFact p (← inferType p) (depth + 1)

/-- The facts about registers among the hypotheses. -/
private meta def scan : MetaM Facts := do
  let mut F : Facts := {}
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    (_, F) ← (addFact d.toExpr (← instantiateMVars d.type)).run F
  return F

/-- A proof of the closed proposition `p` by evaluating its `Decidable` instance in the kernel, as
`decide +kernel` does: the kernel checks a lemma that states `p`.

When the kernel rejects the lemma, `addDecl` keeps its statement in the environment as an axiom,
so that later declarations still elaborate. A proposition that is false must leave no such axiom
behind, so a failure restores the state. -/
private meta def decideKernel? (p : Expr) : MetaM (Option Expr) := do
  if p.hasFVar || p.hasMVar || p.hasLevelParam then return none
  let some inst ← synthInstance? (mkApp (mkConst ``Decidable) p) | return none
  let pf := mkApp3 (mkConst ``of_decide_eq_true) p inst
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  let saved ← saveState
  try
    return some (mkConst (← withOptions (Elab.async.set · false) <| mkAuxLemma [] p pf))
  catch _ =>
    saved.restore
    return none

/-- Prove the premise `p` of a frame: by evaluation if it has no free variables, in the kernel for
`c.Preserves i`, also after unfolding a predicate introduced by `let`, and otherwise by a
hypothesis. -/
private meta def discharge (p : Expr) : MetaM (Option Expr) := do
  let p ← instantiateMVars p
  if p.hasExprMVar then return none
  if p.isAppOf ``Code.Preserves then
    if let some h ← decideKernel? p then return some h
  else if let some r ← WP.Exec.decideClosed? p then
    return r
  else
    let q ← Core.betaReduce (← zetaReduce p)
    if let some (some h) ← WP.Exec.decideClosed? q then return some (← mkExpectedTypeHint h p)
  WP.Exec.assumption? p

/-- Apply the frame `f` to the read `e`, `s'.regs i`: the read `s.regs i` it equals and the proof,
or the premise of `f` that could not be proved. -/
private meta def applyFrame (f : Frame) (e : Expr) :
    MetaM (Except (Option Expr) (Expr × Expr)) :=
  withNewMCtxDepth do
    let (xs, _, body) ← forallMetaTelescopeReducing f.type
    let some (_, lhs, rhs) := body.eq? | return .error none
    unless ← withReducible (isDefEq lhs e) do return .error none
    for x in xs do
      let x' ← instantiateMVars x
      unless x'.isMVar do continue
      let p ← instantiateMVars (← inferType x')
      unless ← isProp p do return .error none
      let some h ← discharge p | return .error (some p)
      x'.mvarId!.assign h
    return .ok (← instantiateMVars rhs, ← instantiateMVars (mkAppN f.proof xs))

/-- The reads that could not be followed further, each with the frames of its state and the
premise of each that could not be proved. -/
private meta abbrev Stuck := Array (Expr × Array (MessageData × Expr))

/-- Follow the read `e`, `s'.regs i`, back: to its value if a hypothesis states it, through
`Data.set` and `Data.write`, through a frame of the state whose premises hold at `i`, and through
the definition of a state introduced by `let`. A state is visited once, so that frames in both
directions between two states do not loop. -/
private meta def frameStep (F : Facts) (stuck : IO.Ref Stuck) (e : Expr) : SimpM Simp.Step := do
  unless (read? e).isSome do return .continue
  let mut cur := e
  let mut proof? : Option Expr := none
  let mut visited : Std.HashSet Expr := {}
  let mut changed := false
  let push (proof? : Option Expr) (h : Expr) : MetaM (Option Expr) := do
    match proof? with
    | none => return some h
    | some p => return some (← mkEqTrans p h)
  repeat
    let some (r, s, i) := read? cur | break
    if visited.contains s then break
    visited := visited.insert s
    if let some (v, h) := F.values[(s, ← regKey r i)]? then
      proof? ← push proof? (← mkExpectedTypeHint h (← mkEq cur v))
      cur := v
      continue
    if let .visit res ← WP.Exec.reduceRegsStep cur then
      proof? ← push proof? (← res.getProof)
      cur := res.expr
      continue
    let mut next? := none
    let mut failed := #[]
    for f in (F.frames.getD s #[]).reverse do
      match ← applyFrame f cur with
      | .ok r =>
        next? := some r
        break
      | .error (some p) => failed := failed.push (f.name, p)
      | .error none => pure ()
    if let some (rhs, h) := next? then
      proof? ← push proof? h
      cur := rhs
      continue
    if let .fvar fv := s then
      if let some val ← fv.getValue? then
        cur := mkApp3 (mkConst ``Data.regs) r val i
        changed := true
        continue
    stuck.modify fun st => if st.any (·.1 == cur) then st else st.push (cur, failed)
    break
  if proof?.isNone && !changed then return .continue
  let res : Simp.Result := { expr := cur, proof? }
  -- A value may itself read registers, as in `y.regs a = x.regs a + 1`.
  return if (read? cur).isSome || (cur.find? (read? · |>.isSome)).isNone then .done res
    else .visit res

/-- Rewrite the reads of registers in `e` along the frames. -/
private meta def frameSimp (F : Facts) (stuck : IO.Ref Stuck) (e : Expr) : MetaM Simp.Result := do
  let ctx ← Simp.mkContext (config := { maxSteps := 20000 })
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Simp.main e ctx (methods := { pre := frameStep F stuck })).1

/-- Split the goal into the components of conjunctions and `Prop`-valued structures. -/
private meta partial def components (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let .const c _ := tgt.getAppFn | return #[g]
  let env ← getEnv
  unless c != ``Iff && isStructure env c && !isClass env c do return #[g]
  let some info := env.find? c | return #[g]
  unless info.type.getForallBody.isProp do return #[g]
  let some gs ← observing? g.constructor | return #[g]
  return (← gs.toArray.mapM components).flatten

/-- Prove the equation `g` along the frames `F`, or return what is left of it. -/
private meta def closeGoal (F : Facts) (stuck : IO.Ref Stuck) (g : MVarId) :
    MetaM (Option Expr) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let res ← frameSimp F stuck tgt
  let g' ← applySimpResultToTarget g tgt res
  let tgt' ← instantiateMVars (← g'.getType)
  -- The value may be left to be inferred, as in `exec_callee x (by regs_frame)`.
  if let some (_, a, b) := tgt'.cleanupAnnotations.eq? then
    if ← isDefEq a b then
      g'.assign (← mkEqRefl a)
      return none
  return some tgt'

end RegsFrame

/-- `regs_frame` proves a fact about the registers after a sequence of calls from the frames of the
calls: an equation such as `z.regs a = v`, a conjunction or `Prop`-valued structure of such
equations, such as `Parameters L H z`, or the frame `∀ i, i ≠ r → i ≠ r' → z.regs i = x.regs i` of
the sequence.

It follows each read `z.regs a` in the goal back to a hypothesis that states the value:

* through a frame among the hypotheses, `yf : ∀ i, i ≠ r → … → z.regs i = y.regs i`, whose
  premises hold at `a`: by evaluation when they have no free variables (a predicate introduced by
  `let` is unfolded first), otherwise by a hypothesis;
* through an execution `he : ExecWithin w c y z T` (or `Exec`, or any `J` with a lemma
  `J.regs_eq`), when the code `c` does not write `a`, which the kernel decides;
* through `Data.set` and `Data.write`, and through the definition of a state introduced by `let`;
* to the value given by `h : x.regs a = v`, or by a component of a conjunction or a field of a
  hypothesis `hx : Parameters L H x`.

When several frames of a state hold at `a`, the tactic follows the latest hypothesis among them and
does not return to the others. A value stated only at an intermediate state that this frame skips
is therefore not found, and the tactic fails with the error described below.

No hypothesis is named, and a value the goal leaves open is filled in, so that the facts a
specification asks for can be given as `exec_callee y (by regs_frame) (by regs_frame)`. When a
read cannot be followed to the stated value, the error shows the equation that is left and, for
each frame of the state it stopped at, the premise that does not hold at the register. -/
syntax (name := regsFrame) "regs_frame" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| regs_frame) => withMainContext do
    -- The goal may be a frame itself: `∀ i, i ≠ r → z.regs i = x.regs i`.
    let (_, g) ← (← getMainGoal).intros
    g.withContext do
      let facts ← RegsFrame.scan
      let stuck ← IO.mkRef #[]
      let mut failures : Array (Expr × Expr) := #[]
      for g in ← RegsFrame.components g do
        let tgt ← g.getType
        if let some left ← RegsFrame.closeGoal facts stuck g then
          failures := failures.push (tgt, left)
      unless failures.isEmpty do
        let mut msg := m!"regs_frame: could not prove"
        for (tgt, left) in failures do
          msg := msg ++ indentExpr tgt
          unless left == tgt do
            msg := msg ++ m!"\nFollowing the frames leaves{indentExpr left}"
          for (e, failed) in ← stuck.get do
            unless (left.find? (· == e)).isSome do continue
            if failed.isEmpty then
              msg := msg ++ m!"\nNo hypothesis gives `{e}` or a frame of its state."
            for (f, p) in failed do
              msg := msg ++ m!"\n`{f}` does not give `{e}`: it needs{indentExpr p}"
        throwError msg
      replaceMainGoal []

end Cslib.WordRAM

end
