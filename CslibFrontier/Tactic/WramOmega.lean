/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.WramOmega.Init
public meta import CslibFrontier.Tactic.WramOmega.Prove
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
`Cslib.WordRAM.Fits w v`, is unfolded in the same way, each power of two `2 ^ e` the tactic
meets is known to be positive, and when two powers `2 ^ e₁` and `2 ^ e₂` occur with `e₁ ≤ e₂` or
`e₁ < e₂` provable by `omega`, `2 ^ e₁ ≤ 2 ^ e₂` (respectively `2 * 2 ^ e₁ ≤ 2 ^ e₂`) is added as
well. So a word-size bound on an address follows from the bound on the end of the layout, also at a
wider word size. The tactic `fits` of `CslibFrontier.Tactic.Fits` proves a word-size bound that
needs no tagged definition unfolded; `wram_omega` is for the other goals, a word-size bound through
tagged definitions among them.

Every tagged definition met is unfolded, and a call cannot keep one folded: where a bound holds
only with a definition folded, the proof stays `unfold a b; omega`.

## Main definitions

* `wram_omega`: prove a linear arithmetic goal, unfolding the `@[wram_arith]` definitions that
  occur.
* `wram_omega_silent`, `Cslib.Tactic.WramOmega.tryProve`: silent, heartbeat-bounded helper used
  by tactic dischargers (`wram_exec`, `wram_simp`, `wram_call`, `mem_frame`, `struct_frame`).
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
  /-- The powers of two met, deduplicated by hash for `0 < 2 ^ k` positivity facts. -/
  powers : ExprSet := {}
  /-- Up to `maxPowerExps` distinct powers of two, in the order met, for pairwise monotonicity. -/
  monoPowers : Array Expr := #[]

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

/-- The most distinct powers of two compared pairwise for monotonicity. -/
private def maxPowerExps : ℕ := 8

/-- The `maxHeartbeats` budget for one exponent comparison `e₁ ≤ e₂`, in thousands. -/
private def maxMonoHeartbeats : ℕ := 20000

/-- A proof of `lhs ≤ rhs` by `omega` from `hyps`, or `none`. -/
private def proveLe? (hyps : List Expr) (lhs rhs : Expr) : MetaM (Option Expr) := do
  proveOmega? maxMonoHeartbeats hyps (← mkAppM ``LE.le #[lhs, rhs])

/-- Proofs of monotonicity between distinct powers of two `(2 ^ e₁, 2 ^ e₂)` in `powers` when
`omega` proves `e₁ < e₂` (`2 * 2 ^ e₁ ≤ 2 ^ e₂`) or `e₁ ≤ e₂` (`2 ^ e₁ ≤ 2 ^ e₂`) from `hyps`.
When more than four powers occur and `initCount > 0` come from the goal or explicit arguments, only
pairs touching one of those `initCount` powers are tested. -/
private def powerMonoFacts (powers : Array Expr) (initCount : ℕ) (hyps : List Expr) :
    MetaM (Array Expr) := do
  let ps := powers.extract 0 maxPowerExps
  if ps.size < 2 then return #[]
  let iBound := if ps.size > 4 && initCount > 0 then min initCount ps.size else ps.size
  let two := mkNatLit 2
  let twoPos := mkApp (mkConst ``Nat.zero_lt_succ) (mkNatLit 1)
  let mkWeak (t₁ e₁ t₂ e₂ hLe : Expr) : MetaM (Option Expr) := do
    let type ← mkAppM ``LE.le #[t₁, t₂]
    let value := mkAppN (mkConst ``Nat.pow_le_pow_right) #[two, twoPos, e₁, e₂, hLe]
    unless ← isDefEq type (← inferType value) do return none
    some <$> mkExpectedTypeHint value type
  let mkStrict (t₁ e₁ t₂ e₂ hLt : Expr) : MetaM (Option Expr) := do
    let succE₁ := mkApp (mkConst ``Nat.succ) e₁
    let hpow := mkAppN (mkConst ``Nat.pow_le_pow_right) #[two, twoPos, succE₁, e₂, hLt]
    let heq := mkApp2 (mkConst ``Nat.pow_succ') two e₁
    let twoMulT₁ ← mkAppM ``HMul.hMul #[two, t₁]
    let type ← mkAppM ``LE.le #[twoMulT₁, t₂]
    let hLeEq ← mkAppM ``Nat.le_of_eq #[← mkEqSymm heq]
    let value ← mkAppM ``Nat.le_trans #[hLeEq, hpow]
    unless ← isDefEq type (← inferType value) do return none
    some <$> mkExpectedTypeHint value type
  let mut out : Array Expr := #[]
  for i in [:iBound] do
    let t₁ := ps[i]!
    let e₁ := t₁.appArg!
    for j in [i + 1:ps.size] do
      let t₂ := ps[j]!
      let e₂ := t₂.appArg!
      if e₁.nat?.isSome && e₂.nat?.isSome then continue
      if let some h₁₂ ← proveLe? hyps e₁ e₂ then
        if let some hLt ← proveLe? hyps (mkApp (mkConst ``Nat.succ) e₁) e₂ then
          if let some fact ← mkStrict t₁ e₁ t₂ e₂ hLt then out := out.push fact
        else
          if let some fact ← mkWeak t₁ e₁ t₂ e₂ h₁₂ then out := out.push fact
          if let some h₂₁ ← proveLe? hyps e₂ e₁ then
            if let some fact ← mkWeak t₂ e₂ t₁ e₁ h₂₁ then out := out.push fact
      else if let some h₂₁ ← proveLe? hyps e₂ e₁ then
        if let some hLt ← proveLe? hyps (mkApp (mkConst ``Nat.succ) e₂) e₁ then
          if let some fact ← mkStrict t₂ e₂ t₁ e₁ hLt then out := out.push fact
        else
          if let some fact ← mkWeak t₂ e₂ t₁ e₁ h₂₁ then out := out.push fact
  return out

/-- Record the powers of two in `e`. -/
private def recordPowers (e : Expr) : UnfoldM Unit :=
  e.forEachWhere isPowerOfTwo fun t => do
    unless t.hasLooseBVars || (← get).powers.contains t do
      modify fun s =>
        { s with
          powers := s.powers.insert t
          monoPowers :=
            if s.monoPowers.size < maxPowerExps then s.monoPowers.push t else s.monoPowers }

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
read from a structure given by its constructor is replaced by its value, every power of two
`2 ^ e` met is known to be positive, and when `omega` proves `e₁ ≤ e₂` or `e₁ < e₂` between two
powers met, `2 ^ e₁ ≤ 2 ^ e₂` (respectively `2 * 2 ^ e₁ ≤ 2 ^ e₂`) is supplied as well.

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
        let pos₁ ← powerFacts
        if (← omegaWith g {} (facts ++ pos₁)).isNone then
          let state ← get
          if state.unfolded.isEmpty && !state.reduced && state.powers.isEmpty && terms.isEmpty then
            Linter.logLintIf linter.unnecessaryWramOmega tk m!"`wram_omega` unfolded no \
              `@[wram_arith]` definition here: `omega` proves this goal."
          return
        let mono₁Candidates := (← get).monoPowers
        if mono₁Candidates.size ≥ 2 then
          let savedMono₁ ← Meta.saveState
          let hyps₁ ← (← getLocalHyps).filterM fun h => do readByOmega (← inferType h)
          let mono₁ ← powerMonoFacts mono₁Candidates mono₁Candidates.size
            (hyps₁ ++ facts ++ pos₁).toList
          if !mono₁.isEmpty then
            if (← omegaWith g {} (facts ++ pos₁ ++ mono₁)).isNone then
              return
          savedMono₁.restore
        -- Then with the local definitions unfolded too, and the arithmetic hypotheses
        -- that mention a tagged definition or a local one restated.
        withReader ({ · with locals := allLocals }) do
          let ctx ← read
          let (g, facts) ← unfoldGoal g
          let initPowers := (← get).monoPowers.size
          let mut facts := facts
          let mut plainArith : Array Expr := #[]
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
              plainArith := plainArith.push d.toExpr
          let posFacts ← powerFacts
          let mut err? ← omegaWith g replaced (facts ++ posFacts)
          let monoCandidates := (← get).monoPowers
          if err?.isSome && monoCandidates.size ≥ 2 then
            let savedMono ← Meta.saveState
            let monoFacts ← powerMonoFacts monoCandidates initPowers
              (plainArith ++ facts ++ posFacts).toList
            unless monoFacts.isEmpty do
              err? ← omegaWith g replaced (facts ++ posFacts ++ monoFacts)
            if err?.isSome then
              savedMono.restore
          let some ex := err? | return
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

/-- Try to prove `g` with `wram_omega` (plus optional extra fact expressions `extra`) without
emitting warnings or exceeding `maxHeartbeats` (in thousands). Returns `true` if `g` is closed; on
failure restores the state and returns `false`. Skips immediately when `g` is not an arithmetic
goal or mentions no `@[wram_arith]` definition, local definition, or power of two anywhere in the
goal, `extra`, or arithmetic hypotheses. -/
def tryProve (g : MVarId) (maxHeartbeats : ℕ := 20000) (extra : Array Expr := #[]) :
    MetaM Bool := do
  let env ← getEnv
  let tagged := wramArithExt.getState env
  let saved ← saveState
  let ok ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let tgtArith ← if isArithmetic tagged tgt then pure true else do
      let .const name _ := tgt.getAppFn | pure false
      if ← isReducible name then pure (isArithmetic tagged (← whnfR tgt)) else pure false
    unless tgtArith do return false
    let (locals, allLocals) ← localDefinitions tagged
    let hasTagOrPow (e : Expr) : Bool :=
      e.getUsedConstants.any tagged.contains ||
        (!allLocals.isEmpty && e.hasAnyFVar allLocals.contains) ||
        (e.find? isPowerOfTwo).isSome
    let tgtHas := hasTagOrPow tgt
    let mut relevant := tgtHas
    if !relevant then
      for h in extra do
        if hasTagOrPow (← instantiateMVars (← inferType h)) then
          relevant := true
          break
    if !relevant then
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        if isArithmetic tagged ty && hasTagOrPow ty then
          relevant := true
          break
    unless relevant do return false
    let attempt : MetaM Bool := do
      let unfoldGoal (g : MVarId) : UnfoldM (MVarId × Array Expr) := do
        let target ← unfoldTagged (← instantiateMVars (← g.getType))
        recordPowers target
        let mut extraFacts := #[]
        for h in extra do
          let ty ← unfoldTagged (← instantiateMVars (← inferType h))
          recordPowers ty
          extraFacts := extraFacts.push (← mkExpectedTypeHint h ty)
        return (← g.replaceTargetDefEq target, extraFacts)
      let prove : UnfoldM Bool := do
        let g ←
          if tgtHas || !extra.isEmpty then
            let (g₁, extra₁) ← unfoldGoal g
            if (← omegaWith g₁ {} (extra₁ ++ (← powerFacts))).isNone then return true
            pure g₁
          else
            pure g
        withReader ({ · with locals := allLocals }) do
          let ctx ← read
          let (g₂, extra₂) ← unfoldGoal g
          let mut facts : Array Expr := extra₂
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
          let st ← get
          if replaced.isEmpty && st.unfolded.isEmpty && !st.reduced && st.powers.isEmpty then
            return false
          return (← omegaWith g₂ replaced (facts ++ (← powerFacts))).isNone
      (prove.run { tagged, locals }).run' {}
    let budget : MetaM Bool :=
      withCurrHeartbeats <| withTheReader Core.Context
        (fun ctx => { ctx with maxHeartbeats := maxHeartbeats * 1000 }) attempt
    tryCatchRuntimeEx budget fun _ => return false
  unless ok do saved.restore
  return ok

/-- Silent, heartbeat-bounded `wram_omega` for use inside tactic dischargers. -/
syntax (name := wramOmegaSilent) "wram_omega_silent" : tactic

elab_rules : tactic
  | `(tactic| wram_omega_silent) => do
    recordExtraModUse (isMeta := false) `Init.Omega
    withMainContext do
      let g ← getMainGoal
      if ← tryProve g then
        replaceMainGoal []
      else
        throwError "wram_omega_silent: could not prove goal"

end Cslib.Tactic.WramOmega

end
