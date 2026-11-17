/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.WramOmega.Init
public meta import Lean.Elab.Tactic.Omega

/-!
# Linear arithmetic over the definitions of a word-RAM development

A word-RAM development states its arithmetic through chains of definitions: addresses and sizes of
a memory layout, such as `tableBase base = base + 20` and
`keysBase base n = tableBase base + tableSize n`, bounds on steps and cost, and numeric parameters.
`omega` reads each application of such a definition as an unknown number, so a proof that compares
addresses first names the definitions to unfold, and has to be revisited when the layout gains a
region.

`wram_omega` proves such a goal from the definitions themselves. They are tagged `@[wram_arith]`
where they are written (the attribute's docstring says which definitions are tagged), and the
tactic unfolds the tagged definitions that occur, also those in the bodies of tagged definitions,
before it runs `omega`. It unfolds them in the goal first, which is what
`unfold tableBase keysBase; omega` does by hand. When `omega` then fails, it also unfolds the local
definitions (`set S := n + 1`), and reads the arithmetic hypotheses unfolded in the same way, as
`dsimp only [tableBase, keysBase, S] at *; omega` does. The hypotheses in the context are not
changed.

A tagged definition that returns a proposition, such as the word-size bound
`Cslib.WordRAM.Fits w v`, is unfolded in the same way, and each power of two `2 ^ e` the tactic
meets is known to be positive, which `omega` does not see by itself. So a word-size bound on an
address follows from the bound on the end of the layout. The tactic `fits` of
`CslibFrontier.Tactic.Fits` proves a word-size bound that needs no tagged definition unfolded;
`wram_omega` is for the other goals, a word-size bound through tagged definitions among them.

Every tagged definition met is unfolded, and a call cannot keep one folded: where a bound holds
only with a definition folded, the proof stays `unfold a b; omega`.

## Main definitions

* `wram_omega`: prove a linear arithmetic goal, unfolding the `@[wram_arith]` definitions that
  occur.
-/

public meta section

namespace Cslib.Tactic.WramOmega

open Lean Meta Elab Tactic

/-- Whether `wram_omega` warns when it unfolded nothing, so that `omega` alone proves the goal. -/
register_option linter.unnecessaryWramOmega : Bool := {
  defValue := true
  descr := "warn when `wram_omega` unfolds no `@[wram_arith]` definition: `omega` proves the goal"
}

/-- Whether `omega` compares numbers of type `α`. -/
private def isNumberType (α : Expr) : Bool :=
  α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1

/-- Whether `omega` reads a hypothesis of type `type` once the tagged predicates are unfolded: a
comparison of numbers, a tagged predicate, or a propositional combination that contains one. -/
private partial def isArithmetic (tagged : NameMap Kind) (type : Expr) : Bool :=
  match_expr type with
  | Eq α _ _ => isNumberType α
  | Ne α _ _ => isNumberType α
  | LE.le α _ _ _ => isNumberType α
  | LT.lt α _ _ _ => isNumberType α
  | GE.ge α _ _ _ => isNumberType α
  | GT.gt α _ _ _ => isNumberType α
  | Dvd.dvd α _ _ _ => isNumberType α
  | Not p => isArithmetic tagged p
  | And p q => isArithmetic tagged p || isArithmetic tagged q
  | Or p q => isArithmetic tagged p || isArithmetic tagged q
  | Iff p q => isArithmetic tagged p || isArithmetic tagged q
  | _ =>
    match type with
    | .forallE _ p q _ =>
      !q.hasLooseBVars && (isArithmetic tagged p || isArithmetic tagged q)
    | .mdata _ b => isArithmetic tagged b
    | _ =>
      match type.getAppFn with
      | .const name _ => tagged.find? name == some .predicate
      | _ => false

/-- What `wram_omega` unfolds. -/
private structure Context where
  /-- The active `@[wram_arith]` definitions. -/
  tagged : NameMap Kind
  /-- The local definitions (`set x := …`) to unfold. -/
  locals : FVarIdSet

/-- What `wram_omega` has met so far. -/
private structure State where
  /-- The tagged definitions unfolded, in the order met. -/
  unfolded : Array Name := #[]
  /-- The tagged definitions met whose bodies are not visible here. -/
  hidden : Array Name := #[]
  /-- Whether a local definition was unfolded, a field of a constructor was read or a `let` was
  reduced: `omega` alone does none of these inside a term. -/
  reduced : Bool := false
  /-- The powers of two met. -/
  powers : Std.HashSet Expr := {}

/-- Unfolds terms, with the active `@[wram_arith]` definitions. -/
private abbrev UnfoldM := ReaderT Context <| StateRefT State MetaM

/-- Whether `e` mentions something `ctx` unfolds. -/
private def Context.mentions (ctx : Context) (e : Expr) : Bool :=
  e.getUsedConstants.any ctx.tagged.contains ||
    (!ctx.locals.isEmpty && e.hasAnyFVar ctx.locals.contains)

/-- The local definitions (`set x := …`): first those whose values mention a definition in
`tagged`, directly or through an earlier local definition, then all of them. -/
private def localDefinitions (tagged : NameMap Kind) : MetaM (FVarIdSet × FVarIdSet) := do
  let mut ctx : Context := { tagged, locals := {} }
  let mut all : FVarIdSet := {}
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some value := d.value? | continue
    all := all.insert d.fvarId
    if ctx.mentions (← instantiateMVars value) then
      ctx := { ctx with locals := ctx.locals.insert d.fvarId }
  return (ctx.locals, all)

/-- `e` with the reducible definitions at its head unfolded. Unlike `whnfR`, this accepts a term
under binders, where bound variables are loose. -/
private partial def unfoldReducibleHead (e : Expr) : MetaM Expr := do
  let .const name us := e.getAppFn | return e
  unless ← isReducible name do return e
  let info ← getConstInfo name
  unless info.hasValue && info.levelParams.length == us.length do return e
  unfoldReducibleHead ((← instantiateValueLevelParams info us).betaRev e.getAppRevArgs)

/-- `t` with a field read from a constructor, as in `(Block.mk base n).base`, replaced by its
value. A tagged definition over a structure reads its fields, and `omega` does not reduce them. The
structure may be an abbreviation of a constructor application, as `L.keys` for
`abbrev keys (L : Layout) : Block := ⟨L.base, L.n⟩`. -/
private def reduceField? (t : Expr) : MetaM (Option Expr) := do
  let .const name _ := t.getAppFn | return none
  let some info ← getProjectionFnInfo? name | return none
  if info.fromClass then return none
  let args := t.getAppArgs
  let some struct := args[info.numParams]? | return none
  let some field ← projectCore? (← unfoldReducibleHead struct) info.i | return none
  return some (mkAppN field (args.extract (info.numParams + 1) args.size))

/-- Unfold in `e` the tagged definitions, those in their bodies, and the local definitions of the
context, read the fields of constructors, and reduce the `let`s that remain. -/
private def unfoldTagged (e : Expr) : UnfoldM Expr := do
  let ctx ← read
  let reduce (t : Expr) : UnfoldM TransformStep := do
    let some t ← reduceField? t | return .continue
    modify fun s => { s with reduced := true }
    return .visit t
  let e ← Core.transform e (post := reduce) (pre := fun t => do
    match t.getAppFn with
    | .fvar fvarId =>
      if ctx.locals.contains fvarId then
        if let some value ← fvarId.getValue? then
          modify fun s => { s with reduced := true }
          return .visit ((← instantiateMVars value).betaRev t.getAppRevArgs)
      return .continue
    | .const name us =>
      unless ctx.tagged.contains name do return .continue
      let info ← getConstInfo name
      unless info.hasValue && info.levelParams.length == us.length do
        unless (← get).hidden.contains name do
          modify fun s => { s with hidden := s.hidden.push name }
        return .continue
      unless (← get).unfolded.contains name do
        modify fun s => { s with unfolded := s.unfolded.push name }
      let value ← instantiateValueLevelParams info us
      return .visit (value.betaRev t.getAppRevArgs (useZeta := true))
    | _ => return .continue)
  -- `omega` reads a `let` inside a term as an unknown.
  unless (e.find? (·.isLet)).isSome do return e
  modify fun s => { s with reduced := true }
  zetaReduce e (zetaDelta := false)

/-- Record the powers of two in `e`. -/
private def recordPowers (e : Expr) : UnfoldM Unit :=
  e.forEachWhere isPowerOfTwo fun t => do
    unless t.hasLooseBVars do modify fun s => { s with powers := s.powers.insert t }

/-- The facts `0 < 2 ^ k` for the powers of two met so far. -/
private def powerFacts : UnfoldM (Array Expr) :=
  return (← get).powers.toArray.map fun t => mkApp (mkConst ``Nat.two_pow_pos) t.appArg!

/-- Whether `omega` reads a hypothesis of type `type`, up to unfolding reducible definitions. -/
private def readByOmega (type : Expr) : UnfoldM Bool := do
  let tagged := (← read).tagged
  if isArithmetic tagged type then return true
  let .const name _ := type.getAppFn | return false
  unless ← isReducible name do return false
  return isArithmetic tagged (← whnfR type)

/-- Close the goal `g` with `omega`, run on `facts` and on the hypotheses other than `replaced`.
When `omega` fails, the state is restored and its error is returned. -/
private def omegaWith (g : MVarId) (replaced : FVarIdSet) (facts : Array Expr) :
    MetaM (Option Exception) := do
  let saved ← saveState
  try
    let some g ← g.falseOrByContra | return none
    g.withContext do
      let type ← g.getType
      let proof ← mkFreshExprSyntheticOpaqueMVar type
      let hyps := (← getLocalHyps).filter fun h => !replaced.contains h.fvarId!
      Omega.omega (hyps ++ facts).toList proof.mvarId!
      -- As `omega` does: its proofs are large, so each is a declaration of its own.
      g.assign (← mkAuxTheorem type (← instantiateMVars proof) (zetaDelta := true))
    return none
  catch ex =>
    saved.restore
    return some ex

/-- `wram_omega` proves a goal of linear arithmetic over `ℕ` and `ℤ` about a word-RAM
development: it unfolds the definitions tagged `@[wram_arith]` (addresses, sizes, cost bounds and
numeric parameters), also those in the bodies of tagged definitions, and runs `omega`. Tagged
predicates, such as the word-size bound `Cslib.WordRAM.Fits`, are unfolded in the same way, a field
read from a structure given by its constructor is replaced by its value, and every power of two
`2 ^ e` met is known to be positive.

The tactic first unfolds the goal only, as `unfold a b; omega` does. When `omega` then fails, it
also unfolds the local definitions (`set S := n + 1`) and reads unfolded the arithmetic hypotheses
that mention a tagged or a local definition, as `dsimp only [a, b, S] at *; omega` does; the
hypotheses in the context are not changed.

`wram_omega [h₁, h₂]` also uses the statements of the terms `h₁` and `h₂`, unfolded like the goal.
Use it for facts `omega` cannot derive, such as bounds on products, and to name the hypotheses
that the goal follows from: `omega` is then run once, on a smaller problem than the one with every
hypothesis unfolded.

Use `fits` for a word-size bound `Fits w v` that needs no tagged definition unfolded. `wram_omega`
is for the other goals: a word-size bound that follows through tagged definitions, as
`Fits w (keysBase base n + i)` from `Fits w (base + space n)`, and a goal of another shape that
uses hypotheses `Fits w v`, which `fits` refuses.

The tactic unfolds every tagged definition it meets; a call cannot keep one folded, and an
untagged definition stays an unknown. Unfolding can lose a bound that holds only with the
definition folded, as when its body divides by a variable. The call then fails, and the proof is
`unfold a b; omega` with the names it needs, as in
`Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compactedEpochWords_mono`. For the same
reason a new `@[wram_arith]` tag can make an existing call fail when its module is built; a call
never proves a different statement.

When `omega` fails, the error lists the definitions that were unfolded and the tagged definitions
whose bodies are not visible in the current module. When nothing was unfolded and `omega` proves
the goal, the linter `linter.unnecessaryWramOmega` asks for `omega`. -/
syntax (name := wramOmega) "wram_omega" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wram_omega%$tk $[[$args,*]]?) => do
    recordExtraModUse (isMeta := false) `Init.Omega
    let tagged := wramArithExt.getState (← getEnv)
    let terms ← ((args.map (·.getElems)).getD #[]).mapM fun t =>
      withMainContext <| elabTerm t none
    liftMetaFinishingTactic fun g => g.withContext do
      let (locals, allLocals) ← localDefinitions tagged
      -- The goal and the given facts, unfolded.
      let unfoldGoal (g : MVarId) : UnfoldM (MVarId × Array Expr) := do
        let target ← unfoldTagged (← instantiateMVars (← g.getType))
        recordPowers target
        let mut facts := #[]
        for h in terms do
          let type ← unfoldTagged (← instantiateMVars (← inferType h))
          recordPowers type
          facts := facts.push (← mkExpectedTypeHint h type)
        return (← g.replaceTargetDefEq target, facts)
      let prove : UnfoldM Unit := do
        -- First the goal only, with the hypotheses as they are.
        let (g, facts) ← unfoldGoal g
        if (← omegaWith g {} (facts ++ (← powerFacts))).isNone then
          let state ← get
          if state.unfolded.isEmpty && !state.reduced && state.powers.isEmpty && terms.isEmpty then
            Linter.logLintIf linter.unnecessaryWramOmega tk m!"`wram_omega` unfolded no \
              `@[wram_arith]` definition here: `omega` proves this goal."
          return
        -- Then with the local definitions unfolded too, and the arithmetic hypotheses
        -- that mention a tagged definition or a local one restated.
        withReader ({ · with locals := allLocals }) do
          let ctx ← read
          let (g, facts) ← unfoldGoal g
          let mut facts := facts
          let mut replaced : FVarIdSet := {}
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            let type ← instantiateMVars d.type
            unless ← readByOmega type do continue
            if ctx.mentions type then
              let type ← unfoldTagged type
              recordPowers type
              facts := facts.push (← mkExpectedTypeHint d.toExpr type)
              replaced := replaced.insert d.fvarId
            else
              recordPowers type
          let some ex ← omegaWith g replaced (facts ++ (← powerFacts)) | return
          let state ← get
          let names (ns : Array Name) :=
            MessageData.joinSep (ns.map (m!"`{.ofConstName ·}`")).toList ", "
          let unfolded := if state.unfolded.isEmpty then
              m!"No `@[wram_arith]` definition occurs in the goal or in an arithmetic hypothesis."
            else m!"Unfolded: {names state.unfolded}."
          let hidden := if state.hidden.isEmpty then m!"" else
            m!"\nTagged `@[wram_arith]` but not unfolded, as their bodies are not visible in \
              this module: {names state.hidden}."
          throwError "wram_omega: `omega` could not prove the goal with the `@[wram_arith]` \
            definitions and the local definitions unfolded in the goal and in the \
            arithmetic hypotheses. Products are unknowns to `omega`: give bounds on them with \
            `wram_omega [h]`.\n{unfolded}{hidden}\n{ex.toMessageData}"
      (prove.run { tagged, locals }).run' {}

end Cslib.Tactic.WramOmega

end
