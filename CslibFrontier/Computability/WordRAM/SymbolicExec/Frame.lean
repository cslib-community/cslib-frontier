/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.RegisterFrame
public import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Register facts across calls

A proof about a word-RAM program that calls subprograms carries the registers it still needs across
each call: the specification of a call gives its result state `y` and a *frame*, a statement
`∀ i, i ≠ r → … → y.regs i = x.regs i` of the registers the call leaves alone, and the proof needs
`y.regs a = v` for every register `a` the next call reads. Written by hand, each such fact names the
frames it passes, proves each of their premises at `a`, and names the hypothesis that gives the
value: `(cf _ (by decide) (by decide)).trans ((bf _ (by decide)).trans ha)`.

`regs_frame` proves these facts from the hypotheses, without naming them, including across renamed
register banks (`Data.comap`, `Data.extend`) and framed calls (`Data.havoc`). `wram_exec *` and
`wram_simp *` use the same context scanner to supply register, frame, and memory-equality rewrites
automatically during symbolic execution.

## Main definitions

* `regs_frame`: prove an equation between register reads and values, a conjunction or `Prop`-valued
  structure of such equations, or a frame, by following each read `y.regs a` back through the
  frames, bank views, and `Data.havoc` layers among the hypotheses to a hypothesis that states the
  value.
* `wram_exec *`, `wram_simp *`: symbolic execution and read simplification automatically resolving
  register equations, frames, bank views, and `y.mem = x.mem` chains from the local context.
-/

public section

namespace Cslib.WordRAM

namespace RegsFrame

open Lean Meta Elab Tactic

/-- A register frame: a proof of a statement `∀ xs, s'.regs i = s.regs i` with `i` among `xs`. -/
meta structure Frame where
  /-- The proof. -/
  proof : Expr
  /-- Its statement. -/
  type : Expr
  /-- How error messages name the frame. -/
  name : MessageData

/-- The facts about registers and whole-memory / cell equalities among the hypotheses. -/
meta structure Facts where
  /-- The frames, by their later state `s'`. -/
  frames : Std.HashMap Expr (Array Frame) := {}
  /-- The values: `(s, a) ↦ (v, h)` for `h : s.regs a = v` (or `f a = v` for `f : Fin r → ℕ`). -/
  values : Std.HashMap (Expr × Expr) (Expr × Expr) := {}
  /-- Memory equalities: `s' ↦ (s, h)` for `h : s'.mem = s.mem`. -/
  memEqs : Std.HashMap Expr (Expr × Expr) := {}
  /-- Memory cell values: `(s, a) ↦ (v, h)` for `h : s.mem a = v`. -/
  memValues : Std.HashMap (Expr × Expr) (Expr × Expr) := {}

/-- The parts `(r, s, i)` of a read `s.regs i` of a register of `s : Data r`. -/
meta def read? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``Data.regs 3 then some (e.getArg! 0, e.getArg! 1, e.getArg! 2) else none

/-- The parts `(r, v, i)` of a bare register-bank function read `v i` (`v : Fin r → ℕ` local fvar),
such as `v` introduced by `wram_call … framed with v m post`. -/
private meta def finFnRead? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let .app v i := e.cleanupAnnotations | return none
  unless v.isFVar do return none
  unless (← inferType e).isConstOf ``Nat do return none
  let_expr Fin r := ← whnfR (← inferType i) | return none
  return some (r, v, i)

/-- The parts `(r, s, a)` of a memory read `s.mem a` of `s : Data r`. -/
private meta def memRead? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``Data.mem 3 then some (e.getArg! 0, e.getArg! 1, e.getArg! 2) else none

/-- The parts `(r, s)` of a whole-memory projection `s.mem`. -/
private meta def memProj? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Data.mem 2 then some (e.getArg! 0, e.getArg! 1) else none

/-- The key of the register name `i : Fin r`: its value if it evaluates to a literal, so that
`Reg.levels` and `(3 : Fin 64)` are the same register, and otherwise the name itself. -/
meta def regKey (r i : Expr) : MetaM Expr := do
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
  if let some (α, lhs, rhs) := ty.eq? then
    let αR ← whnfR α
    if αR.isAppOfArity ``Data 1 then
      let r := αR.appArg!
      let lhsC := lhs.cleanupAnnotations
      let rhsC := rhs.cleanupAnnotations
      if lhsC != rhsC && (rhsC.find? (· == lhsC)).isNone then
        let pfRegs ← withLocalDeclD `i (mkApp (mkConst ``Fin) r) fun i => do
          let hRegs ← mkAppM ``congrArg #[mkApp (mkConst ``Data.regs) r, h]
          mkLambdaFVars #[i] (← mkCongrFun hRegs i)
        addFrame { proof := pfRegs, type := ← inferType pfRegs, name := m!"{h}" } lhsC
        let pfMem ← mkAppM ``congrArg #[mkApp (mkConst ``Data.mem) r, h]
        modify fun F => { F with memEqs := F.memEqs.insert lhsC (rhsC, pfMem) }
      return
    if let some (r, s, i) := read? lhs then
      if (rhs.find? (· == lhs)).isSome then return
      let key := (s, ← regKey r i)
      -- A value is not replaced by an equation between two reads of the register.
      if !((read? rhs).isSome && (← get).values.contains key) then
        modify fun F => { F with values := F.values.insert key (rhs, h) }
      -- When `h : (parent.comap f).regs i = rhs`, also record `(parent, f i) ↦ rhs` so reads with
      -- different syntactic wrappers around `Data.comap` (e.g. `64` vs `BoxTable.registers`) share
      -- the canonical key on `parent`.
      if s.isAppOfArity ``Data.comap 4 then
        let args := s.getAppArgs
        let pKey := (args[3]!, ← regKey args[1]! (mkApp args[2]! i))
        if !((read? rhs).isSome && (← get).values.contains pKey) then
          modify fun F => { F with values := F.values.insert pKey (rhs, h) }
    else if let some (_, s') := memProj? lhs then
      if let some (_, s) := memProj? rhs then
        if s' != s then
          modify fun F => { F with memEqs := F.memEqs.insert s' (s, h) }
    else if let some (_, s, a) := memRead? lhs then
      if (rhs.find? (· == lhs)).isSome then return
      let key := (s, a)
      if (memRead? rhs).isSome && (← get).memValues.contains key then return
      modify fun F => { F with memValues := F.memValues.insert key (rhs, h) }
    else if let some (r, v, i) ← finFnRead? lhs then
      if (rhs.find? (· == lhs)).isSome then return
      let key := (v, ← regKey r i)
      unless (← get).values.contains key do
        modify fun F => { F with values := F.values.insert key (rhs, h) }
    return
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
meta def scan : MetaM Facts := do
  let mut F : Facts := {}
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    (_, F) ← (addFact d.toExpr (← instantiateMVars d.type)).run F
  return F

/-- A proof of `Function.Injective f` for a register map `f : Fin r → Fin s`: checks local
context, standard `Fin` embeddings (`castAdd`, `castLE`, `natAdd`), linear `Fin.mk` definitions
via `omega` on `Fin.val`, and closed `decide`. -/
meta def proveBankInjective? (f : Expr) : MetaM (Option Expr) :=
    withAtLeastTransparency .default do
  let f ← instantiateMVars f
  if let some hf ← WP.Exec.injective? f then return some hf
  match f.getAppFn.constName? with
  | some ``Fin.castAdd =>
    let args := f.getAppArgs
    if args.size == 2 then
      return some (mkApp2 (mkConst ``Fin.castAdd_injective) args[0]! args[1]!)
  | some ``Fin.castLE =>
    let args := f.getAppArgs
    if args.size == 3 then
      return some (mkApp3 (mkConst ``Fin.castLE_injective) args[1]! args[0]! args[2]!)
  | some ``Fin.natAdd =>
    let args := f.getAppArgs
    if args.size == 2 then
      return some (mkApp2 (mkConst ``Fin.natAdd_injective) args[0]! args[1]!)
  | _ => pure ()
  let fty ← whnf (← inferType f)
  let .forallE _ dom cod _ := fty | return none
  let_expr Fin r := ← whnfR dom | return none
  let_expr Fin s := ← whnfR cod | return none
  let saved ← saveState
  -- Unfold a linear `Fin.mk` / `Fin.castAdd` / `Fin.castLE` / `Fin.natAdd` wrapper directly using
  -- `omega` on `Fin.val` (handles e.g. `boxBank : Fin 64 → Fin 160` in O(1), no 64×64 `decide`).
  try
    let hp ← mkAppM ``Function.Injective #[f]
    let g ← mkFreshExprSyntheticOpaqueMVar hp
    let (fv, g1) ← g.mvarId!.introN 3
    let ok ← g1.withContext do
      let x := mkFVar fv[0]!
      let y := mkFVar fv[1]!
      let h := mkFVar fv[2]!
      let valEq ← mkAppM ``congrArg #[mkApp (mkConst ``Fin.val) s, h]
      let fx ← whnfD (mkApp f x)
      let fy ← whnfD (mkApp f y)
      let vx? := if fx.isAppOfArity ``Fin.mk 3 then some (fx.getArg! 1) else none
      let vy? := if fy.isAppOfArity ``Fin.mk 3 then some (fy.getArg! 1) else none
      match vx?, vy? with
      | some vx, some vy =>
        let eqTy ← mkEq vx vy
        let valGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq (mkApp2 (mkConst ``Fin.val) r x)
          (mkApp2 (mkConst ``Fin.val) r y))
        if ← isDefEq (← inferType valEq) eqTy then
          let hval ← mkExpectedTypeHint valEq eqTy
          let some gContra ← valGoal.mvarId!.falseOrByContra | return false
          let ok ← gContra.withContext do
            let some neg := (← getLCtx).lastDecl | return false
            Lean.Elab.Tactic.Omega.omega [neg.toExpr, hval] gContra
            return true
          unless ok do return false
          g1.assign (mkApp4 (mkConst ``Fin.ext) r x y (← instantiateMVars valGoal))
          return true
        else
          return false
      | _, _ => return false
    if ok then
      return some (← instantiateMVars g)
  catch _ => pure ()
  saved.restore
  let hp ← mkAppM ``Function.Injective #[f]
  if let some (some hf) ← WP.Exec.decideClosed? hp then return some hf
  return none

/-- Prove `c.Preserves i` structurally across `.seq`, `.branch`, `.loop`, `.op`, `.rand`, and
`.rename` without requiring `c` to be closed (so e.g. `storeHeaderPart2 k` with a free `k : ℕ`
works when `k` only appears inside constant operands). -/
private meta partial def provePreserves? (c i : Expr) (fuel : ℕ := 64) :
    MetaM (Option Expr) := withAtLeastTransparency .default do
  if fuel == 0 then return none
  let c ← whnfD c
  match c.getAppFn.constName? with
  | some ``Code.seq =>
    let args := c.getAppArgs
    unless args.size == 4 do return none
    let some h1 ← provePreserves? args[2]! i (fuel - 1) | return none
    let some h2 ← provePreserves? args[3]! i (fuel - 1) | return none
    mkAppM ``And.intro #[h1, h2]
  | some ``Code.branch =>
    let args := c.getAppArgs
    unless args.size == 5 do return none
    let some h1 ← provePreserves? args[3]! i (fuel - 1) | return none
    let some h2 ← provePreserves? args[4]! i (fuel - 1) | return none
    mkAppM ``And.intro #[h1, h2]
  | some ``Code.loop =>
    let args := c.getAppArgs
    unless args.size == 4 do return none
    provePreserves? args[3]! i (fuel - 1)
  | some ``Code.op =>
    let args := c.getAppArgs
    unless args.size == 3 do return none
    let B := args[0]!
    let r := args[1]!
    let o := args[2]!
    let dest ← whnfD (mkApp3 (mkConst ``Op.dest) B r o)
    match_expr dest with
    | Option.none _ =>
      let pf ← mkAppM ``Ne.symm #[← mkAppM ``Option.some_ne_none #[i]]
      let p ← mkAppM ``Code.Preserves #[i, c]
      if ← isDefEq (← inferType pf) p then return some (← mkExpectedTypeHint pf p)
      return none
    | Option.some _ d =>
      let p ← mkAppM ``Code.Preserves #[i, c]
      let some dv ← WP.Exec.regValue? r d | return none
      let some iv ← WP.Exec.regValue? r i | return none
      if dv == iv then return none
      let hne ← mkDecideProof (mkNot (← mkEq d i))
      let someD ← mkAppM ``Option.some #[d]
      let someI ← mkAppM ``Option.some #[i]
      let pf ← withLocalDeclD `h (← mkEq someD someI) fun h => do
        let heq ← mkAppM ``Option.some.inj #[h]
        mkLambdaFVars #[h] (mkApp hne heq)
      if ← isDefEq (← inferType pf) p then return some (← mkExpectedTypeHint pf p)
      return none
    | _ => return none
  | some ``Code.rand =>
    let args := c.getAppArgs
    unless args.size == 4 do return none
    let r := args[1]!
    let dst := args[2]!
    let some dv ← WP.Exec.regValue? r dst | return none
    let some iv ← WP.Exec.regValue? r i | return none
    if dv == iv then return none
    return some (← mkDecideProof (mkNot (← mkEq dst i)))
  | some ``Code.rename =>
    let args := c.getAppArgs
    unless args.size == 5 do return none
    let f := args[3]!
    let sub := args[4]!
    if let some hne ← WP.Exec.forallRangeNe? f i then
      return some (← mkAppM ``Code.preserves_rename_of_forall_ne #[sub, f, i, hne])
    let pne ← withLocalDeclD `j (mkApp (mkConst ``Fin) args[1]!) fun j => do
      mkForallFVars #[j] (mkNot (← mkEq (mkApp f j) i))
    if let some (some hne) ← WP.Exec.decideClosed? pne then
      return some (← mkAppM ``Code.preserves_rename_of_forall_ne #[sub, f, i, hne])
    return none
  | _ => return none

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

/-- Prove the premise `p` of a frame: by evaluation if it has no free variables, in the kernel (or
structurally for parameterized programs) for `c.Preserves i`, also after unfolding a predicate
introduced by `let`, and otherwise by a hypothesis. -/
private meta def discharge (p : Expr) : MetaM (Option Expr) := do
  let p ← instantiateMVars p
  if p.hasExprMVar then return none
  if p.isAppOf ``Code.Preserves then
    if let some h ← decideKernel? p then return some h
    if p.getAppArgs.size == 4 then
      let saved ← saveState
      try
        if let some h ← provePreserves? (p.getArg! 3) (p.getArg! 2) then
          return some h
      catch _ => pure ()
      saved.restore
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
meta abbrev Stuck := Array (Expr × Array (MessageData × Expr))

/-- Reduce a single register read `d.regs j` across `Data.extend`:
* `(y.extend f x).regs (f i) = y.regs i` using `proveBankInjective? f`
* `(y.extend f x).regs j = x.regs j` when a hypothesis gives `j ∉ Set.range f` or `∀ k, f k ≠ j`
* `Fin.castAdd` / `Fin.castLE` / `Fin.natAdd` numeric and symbolic embeddings
* closed finite banks `f : Fin n → Fin s` with literal `j`. -/
meta def reduceExtendRegs? (r s f y x j : Expr) : MetaM (Option (Expr × Expr)) :=
    withAtLeastTransparency .default do
  if let .app f' a := j then
    if f' == f then
      if let some hf ← proveBankInjective? f then
        let hEq ← mkEqRefl j
        let pf ← mkAppM ``Data.extend_regs_of_eq #[hf, y, x, a, j, hEq]
        return some (mkApp3 (mkConst ``Data.regs) r y a, pf)
  if let some hne ← WP.Exec.forallRangeNe? f j then
    let pf ← mkAppM ``Data.extend_regs_of_forall_ne #[y, x, j, hne]
    return some (mkApp3 (mkConst ``Data.regs) s x j, pf)
  let saved ← saveState
  try
    let rangeF ← mkAppM ``Set.range #[f]
    let memNot := mkNot (← mkAppM ``Membership.mem #[rangeF, j])
    if let some hj ← WP.Exec.assumption? memNot then
      let pf ← mkAppM ``Data.extend_regs_of_notMem #[y, x, hj]
      return some (mkApp3 (mkConst ``Data.regs) s x j, pf)
  catch _ => saved.restore
  if f.isAppOfArity ``Fin.castLE 3 then
    let rVal? ← getNatValue? (← whnf r)
    let jVal? ← WP.Exec.regValue? s j
    if let (some rv, some jv) := (rVal?, jVal?) then
      if jv < rv then
        let i ← mkNumeral (mkApp (mkConst ``Fin) r) jv
        if let some hf ← proveBankInjective? f then
          let hEq ← mkDecideProof (← mkEq (mkApp f i) j)
          let pf ← mkAppM ``Data.extend_regs_of_eq #[hf, y, x, i, j, hEq]
          return some (mkApp3 (mkConst ``Data.regs) r y i, pf)
      else
        let hle ← mkDecideProof (← mkAppM ``LE.le #[r, mkApp2 (mkConst ``Fin.val) s j])
        let pf ← mkAppOptM ``Data.extend_castLE_regs_of_le
          #[some r, some s, some (f.getArg! 2), some y, some x, some j, some hle]
        return some (mkApp3 (mkConst ``Data.regs) s x j, pf)
  let some n ← getNatValue? (← whnf r) | return none
  let some jv ← WP.Exec.regValue? s j | return none
  if jv < n then
    let i ← mkNumeral (mkApp (mkConst ``Fin) r) jv
    if let some iv ← WP.Exec.regValue? s (mkApp f i) then
      if iv == jv then
        if let some hf ← proveBankInjective? f then
          let h ← mkDecideProof (← mkEq (mkApp f i) j)
          let pf ← mkAppM ``Data.extend_regs_of_eq #[hf, y, x, i, j, h]
          return some (mkApp3 (mkConst ``Data.regs) r y i, pf)
  if n ≤ 64 then
    for k in [:n] do
      let i ← mkNumeral (mkApp (mkConst ``Fin) r) k
      let some iv ← WP.Exec.regValue? s (mkApp f i) | return none
      if iv == jv then
        let some hf ← proveBankInjective? f | return none
        let h ← mkDecideProof (← mkEq (mkApp f i) j)
        let pf ← mkAppM ``Data.extend_regs_of_eq #[hf, y, x, i, j, h]
        return some (mkApp3 (mkConst ``Data.regs) r y i, pf)
    let hp := mkAppN (mkConst ``Data.extend_regs_of_forall_ne) #[r, s, f, y, x, j]
    let .forallE _ p _ _ ← inferType hp | return none
    if let some (some hi) ← WP.Exec.decideClosed? p then
      return some (mkApp3 (mkConst ``Data.regs) s x j, mkApp hp hi)
  return none

/-- Reduce `(s.comap f).regs i`: first cancel `(y.extend f x).comap f = y` (peeking through a
`let`-binding `u := y.extend f x` without losing `y`), then otherwise unfold to `s.regs (f i)`. -/
private meta def reduceComapRegs? (r s f x i : Expr) : MetaM (Option (Expr × Expr)) := do
  let xExpanded ← match x with
    | .fvar fv => do
      match ← fv.getValue? with
      | some v => pure v
      | none => pure x
    | _ => pure x
  match_expr xExpanded with
  | Data.extend r' _ f' y caller =>
    if (← isDefEq f f') then
      if let some hf ← proveBankInjective? f then
        let hComap ← mkAppM ``Data.comap_extend #[hf, y, caller]
        let regFn ← withLocalDeclD `_d (mkApp (mkConst ``Data) r') fun d =>
          mkLambdaFVars #[d] (mkApp3 (mkConst ``Data.regs) r' d i)
        let pf ← mkCongrArg regFn hComap
        return some (mkApp3 (mkConst ``Data.regs) r' y i, pf)
    let pf := mkAppN (mkConst ``Data.comap_regs) #[r, s, f, x, i]
    return some (mkApp3 (mkConst ``Data.regs) s x (mkApp f i), pf)
  | _ =>
    let pf := mkAppN (mkConst ``Data.comap_regs) #[r, s, f, x, i]
    return some (mkApp3 (mkConst ``Data.regs) s x (mkApp f i), pf)

/-- Reduce `(x.havoc c v m).regs i` when `SymbolicExec.Havoc` is imported: to `x.regs i` when
`c.Preserves i` holds (by kernel decision, structural check on parameterized code, or hypothesis),
and to `v i` when `¬c.Preserves i` holds. -/
private meta def reduceHavocRegs? (B r c x v m i : Expr) : MetaM (Option (Expr × Expr)) := do
  let env ← getEnv
  let presLem := `Cslib.WordRAM.Data.havoc_regs_of_preserves
  let notPresLem := `Cslib.WordRAM.Data.havoc_regs_of_not_preserves
  unless env.contains presLem do return none
  let presProp := mkApp4 (mkConst ``Code.Preserves) B r i c
  if let some hp ← discharge presProp then
    let pf ← mkAppOptM presLem
      #[some B, some r, some c, some i, some hp, some x, some v, some m]
    return some (mkApp3 (mkConst ``Data.regs) r x i, pf)
  if env.contains notPresLem then
    let notPresProp := mkNot presProp
    let hnp? ← match ← WP.Exec.decideClosed? notPresProp with
      | some (some h) => pure (some h)
      | _ => WP.Exec.assumption? notPresProp
    if let some hnp := hnp? then
      let pf ← mkAppOptM notPresLem
        #[some B, some r, some c, some i, some hnp, some x, some v, some m]
      return some (mkApp v i, pf)
  return none

/-- Follow the read `e`, `s'.regs i`, back: to its value if a hypothesis states it, through
`Data.set`, `Data.write`, `Data.extend`, `Data.comap`, and `Data.havoc`, through a frame of the
state whose premises hold at `i`, and through the definition of a state introduced by `let`. A
state is visited once, so that frames in both directions between two states do not loop. -/
private meta def frameStep (F : Facts) (stuck : IO.Ref Stuck) (e : Expr) : SimpM Simp.Step := do
  let isFinFn := (← finFnRead? e).isSome
  unless (read? e).isSome || isFinFn do return .continue
  let mut cur := e
  let mut proof? : Option Expr := none
  let mut visited : Std.HashSet Expr := {}
  let mut changed := false
  let push (proof? : Option Expr) (h : Expr) : MetaM (Option Expr) := do
    match proof? with
    | none => return some h
    | some p => return some (← mkEqTrans p h)
  repeat
    let some (r, s, i) := read? cur | do
      if let some (r, v, i) ← finFnRead? cur then
        if !visited.contains v then
          visited := visited.insert v
          if let some (val, h) := F.values[(v, ← regKey r i)]? then
            proof? ← push proof? (← mkExpectedTypeHint h (← mkEq cur val))
            cur := val
            continue
      break
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
    if s.isAppOfArity ``Data.extend 5 then
      let args := s.getAppArgs
      if let some (rhs, h) ← reduceExtendRegs? args[0]! args[1]! args[2]! args[3]! args[4]! i then
        proof? ← push proof? (← mkExpectedTypeHint h (← mkEq cur rhs))
        cur := rhs
        continue
    if s.isAppOfArity ``Data.comap 4 then
      let args := s.getAppArgs
      if let some (rhs, h) ← reduceComapRegs? args[0]! args[1]! args[2]! args[3]! i then
        proof? ← push proof? (← mkExpectedTypeHint h (← mkEq cur rhs))
        cur := rhs
        continue
    if s.isAppOfArity `Cslib.WordRAM.Data.havoc 6 then
      let args := s.getAppArgs
      if let some (rhs, h) ←
          reduceHavocRegs? args[0]! args[1]! args[2]! args[3]! args[4]! args[5]! i then
        proof? ← push proof? (← mkExpectedTypeHint h (← mkEq cur rhs))
        cur := rhs
        continue
    if let .fvar fv := s.getAppFn then
      if let some val ← fv.getValue? then
        let s' := (mkAppN val s.getAppArgs).headBeta
        cur := mkApp3 (mkConst ``Data.regs) r s' i
        changed := true
        continue
    stuck.modify fun st => if st.any (·.1 == cur) then st else st.push (cur, failed)
    break
  if proof?.isNone && !changed then return .continue
  let res : Simp.Result := { expr := cur, proof? }
  -- A value may itself read registers, as in `y.regs a = x.regs a + 1`.
  return if (read? cur).isSome || (cur.find? (read? · |>.isSome)).isSome == false then .done res
    else .visit res

/-- Rewrite the reads of registers in `e` along the frames. -/
meta def frameSimp (F : Facts) (stuck : IO.Ref Stuck) (e : Expr) : MetaM Simp.Result := do
  let ctx ← Simp.mkContext (config := { maxSteps := 20000 })
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Simp.main e ctx (methods := { pre := frameStep F stuck })).1

/-- Split the goal into the components of conjunctions and `Prop`-valued structures. -/
meta partial def components (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let .const c _ := tgt.getAppFn | return #[g]
  let env ← getEnv
  unless c != ``Iff && isStructure env c && !isClass env c do return #[g]
  let some info := env.find? c | return #[g]
  unless info.type.getForallBody.isProp do return #[g]
  let some gs ← observing? g.constructor | return #[g]
  return (← gs.toArray.mapM components).flatten

/-- Prove the equation `g` along the frames `F`, or return what is left of it. -/
meta def closeGoal (F : Facts) (stuck : IO.Ref Stuck) (g : MVarId) :
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
  if !tgt'.hasExprMVar then
    if let some h ← WP.Exec.assumption? tgt' then
      g'.assign h
      return none
  return some tgt'

/-- Attempt to close `g` with `regs_frame` (including `intros` and structure splitting).
Restores the state and returns `false` on failure. -/
meta def tryProve (g : MVarId) (facts? : Option Facts := none) : MetaM Bool := do
  let saved ← saveState
  let ok ← try
    let (_, g') ← g.intros
    g'.withContext do
      let facts ← match facts? with
        | some F => pure F
        | none => scan
      let stuck ← IO.mkRef #[]
      for g'' in ← components g' do
        if (← closeGoal facts stuck g'').isSome then
          return false
      return true
  catch _ => return false
  unless ok do saved.restore
  return ok

/-- One-step `wram_exec *` pre-simproc: reduces a leaf register read `s.regs i` or memory read
`s.mem a` using local values, frames (including `Exec`/`ExecWithin.regs_eq`), `Data.extend`,
`Data.comap`, `Data.havoc`, and `s'.mem = s.mem` equations scanned from context. -/
private meta def autoReadPre (F : Facts) (e : Expr) : SimpM Simp.Step := do
  if let some (_, s, _) := read? e then
    if s.isAppOf ``Data.set || s.isAppOf ``Data.write then
      return .continue
    let stuck ← IO.mkRef #[]
    let step ← frameStep F stuck e
    match step with
    | .done res => return .visit res
    | .visit res => return .visit res
    | .continue _ => return .continue
  if let some (r, s, a) := memRead? e then
    if let some (v, h) := F.memValues[(s, a)]? then
      return .visit { expr := v, proof? := some (← mkExpectedTypeHint h (← mkEq e v)) }
    if let some (sPrev, h) := F.memEqs[s]? then
      let pf ← mkCongrFun h a
      let rhs := mkApp3 (mkConst ``Data.mem) r sPrev a
      return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }
  return .continue

/-- Rewrite the leaf register and memory reads in `e` using `F` (register equations, frames,
`Exec`/`ExecWithin.regs_eq`, `Data.extend`/`Data.comap`/`Data.havoc`, `s'.mem = s.mem`, and
`s.mem a = v`). -/
meta def autoReadSimp (F : Facts) (e : Expr) : MetaM Simp.Result := do
  let hasRead := (e.find? fun t => (read? t).isSome || (memRead? t).isSome).isSome
  unless hasRead do return { expr := e }
  let ctx ← Simp.mkContext (config := { maxSteps := 20000 })
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Simp.main e ctx (methods := { pre := autoReadPre F })).1

end RegsFrame

/-- `wram_exec *` executes structured word-RAM code just like `wram_exec`, and additionally resolves
register reads (`s.regs i`), frames (`∀ i, ... → y.regs i = x.regs i`, `Exec`/`ExecWithin.regs_eq`),
bank views (`Data.extend`/`Data.comap`), `Data.havoc`, memory equalities (`y.mem = x.mem`), and
pointwise memory facts (`x.mem a = v`) from the local context automatically, so callers need not
list `[h0, h1, h2, ...]` by hand. -/
tactic_extension wramExec

@[tactic_alt wramExec]
syntax (name := wramExecStar) "wram_exec" "*" Lean.Parser.Tactic.optConfig
  (Lean.Parser.Tactic.discharger)?
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_exec * $cfg:optConfig $[$d?:discharger]? $[[$args,*]]?) => withMainContext do
    let mut split := true
    for item in cfg.raw[0].getArgs do
      match item[0] with
      | `(Lean.Parser.Tactic.negConfigItem| -split) => split := false
      | `(Lean.Parser.Tactic.posConfigItem| +split) => split := true
      | _ => throwErrorAt item "wram_exec*: unknown option; the only option is `-split`"
    let autoWram := wram.exec.autoWramOmega.get (← getOptions)
    let userDisch ← liftMacroM <| WP.Exec.dischOf d? autoWram
    let disch ← `(tactic| ($userDisch))
    let args := args.map (·.getElems.map (·.raw)) |>.getD #[]
    let facts ← RegsFrame.scan
    WP.Exec.withSimpContext userDisch args fun ctx simprocs simpDischarge => do
      let sideGoals ← IO.mkRef #[]
      let steps ← IO.mkRef 0
      let (g, eq, exact) ← WP.Exec.toWP (← getMainGoal)
      let cfg : WP.Exec.Config := {
        ctx, simprocs, simpDischarge, disch, sideGoals, steps, split
        extraSimp? := some (RegsFrame.autoReadSimp facts)
      }
      let mains ← WP.Exec.walk cfg g
      if (← cfg.steps.get) == 0 then
        let tgt ← instantiateMVars (← g.getType)
        throwError "wram_exec*: nothing to execute in{indentExpr tgt}\nThe program starts with a \
          loop, a random sample or a program given by name. Apply its specification with \
          `WP.of_execWithin`, or unfold it."
      let mains ← mains.filterMapM (WP.Exec.closeBound cfg eq exact)
      replaceMainGoal (mains ++ (← cfg.sideGoals.get)).toList

/-- `wram_simp *` simplifies reads of registers and memory like `wram_simp`, also resolving local
register facts, frames, `Data.extend`/`Data.comap`/`Data.havoc`, and `s'.mem = s.mem` chains
automatically. -/
tactic_extension wramSimp

@[tactic_alt wramSimp]
syntax (name := wramSimpStar) "wram_simp" "*" (Lean.Parser.Tactic.discharger)?
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_simp * $[$d?:discharger]? $[[$args,*]]?) => withMainContext do
    let args := args.map (·.getElems.map (·.raw)) |>.getD #[]
    let autoWram := wram.exec.autoWramOmega.get (← getOptions)
    let facts ← RegsFrame.scan
    WP.Exec.withSimpContext (← liftMacroM <| WP.Exec.dischOf d? autoWram) args
      fun ctx simprocs disch => do
        let g ← getMainGoal
        let tgt ← instantiateMVars (← g.getType)
        let r1 := (← Lean.Meta.simp tgt ctx simprocs (some disch)).1
        let g1 ← applySimpResultToTarget g tgt r1
        let tgt1 ← instantiateMVars (← g1.getType)
        let r2 ← RegsFrame.autoReadSimp facts tgt1
        let g2 ← applySimpResultToTarget g1 tgt1 r2
        let tgt2 ← instantiateMVars (← g2.getType)
        let r3 := (← Lean.Meta.simp tgt2 ctx simprocs (some disch)).1
        let g3 ← applySimpResultToTarget g2 tgt2 r3
        if (← instantiateMVars (← g3.getType)).isTrue then
          g3.assign (mkConst ``True.intro)
          replaceMainGoal []
        else
          replaceMainGoal [g3]

/-- `regs_frame` proves a fact about the registers after a sequence of calls from the frames of the
calls: an equation such as `z.regs a = v`, a conjunction or `Prop`-valued structure of such
equations, such as `Parameters L H z`, or the frame `∀ i, i ≠ r → i ≠ r' → z.regs i = x.regs i` of
the sequence.

It follows each read `z.regs a` in the goal back to a hypothesis that states the value:

* through a frame among the hypotheses, `yf : ∀ i, i ≠ r → … → z.regs i = y.regs i`, whose
  premises hold at `a`: by evaluation when they have no free variables (a predicate introduced by
  `let` is unfolded first), otherwise by a hypothesis;
* through an execution `he : ExecWithin w c y z T` (or `Exec`, or any `J` with a lemma
  `J.regs_eq`), when the code `c` does not write `a`, decided in the kernel when `c` is closed and
  structurally when `c` contains parameters;
* through `Data.set`, `Data.write`, `Data.extend`, `Data.comap`, `Data.havoc`, and the definition
  of a state introduced by `let`;
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
