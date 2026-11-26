/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.MemoryView
public import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
public import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame

/-!
# Mixed-record frame transport tactic

Word-RAM proofs routinely package persistent state predicates as a `Prop`-valued `structure`
(such as `ImpFrame`, `KargerFrame`, or `Schoening.Frame`) or a `Prop`-valued conjunction
definition (such as `HeaderConstsRep`, `TableSlotsRep`, `KeysValsRep`, or `Instances.Output`)
mixing register equations, memory equations, `Block.Realizes` / `Block.HoldsList` views,
quantified cell invariants, and state-independent bounds (`≤`, `Nodup`, `Fits`).

When a state `y` steps to a later state `z` (through `Data.set` / `Data.write` / `Data.havoc`
updates, equalities `z.regs = y.regs` / `z.mem = y.mem`, execution frames, `Modifies`, `Set.EqOn`,
or quantified memory frames `∀ a, P a → z.mem a = y.mem a`), transporting `h : S … y` to `S … z`
otherwise requires a hand-written `.congr` / `.reframe` theorem and per-file macro for every
record type.

`struct_frame` pairs each leaf field of the goal `S … z` 1-to-1 with the matching field of
`h : S … y` and closes:

* unchanged (`isDefEq`) or `rfl` fields (`Nodup`, `Fits`, bounds, self-frame tail);
* register equations, using `regs_frame` (`RegsFrame.tryProve`) or `wram_simp` / `hregs`;
* `Block.Realizes`, `Block.HoldsList`, and `HeapAssertion.holds` fields, using `ram_keep`
  against local updates, `Modifies`, `Set.EqOn`, or quantified memory frames;
* memory equations `m' a = v` and quantified invariants `∀ x, P x → …` (including transparent
  wrapper predicates such as `PartialAt` or nested reads `s k = some (m' a)`), using `mem_frame`
  (`MemFrame.tryProve`) and direct frame rewriting (discharging index bounds with `omega`,
  `decide`, and silent `@[wram_arith]` unfolding, automatically supplying `Fin.isLt` and non-state
  bounds from `h`).

Any field whose nonlinear arithmetic side condition cannot be discharged automatically is left
as a focused subgoal with `h`'s corresponding field already introduced so the proof only has to
supply the missing bound.

## Main definitions

* `struct_frame`: the tactic (`struct_frame` or `struct_frame h`).
-/

public section

namespace Cslib.WordRAM

namespace StructFrame

open Lean Meta Elab Tactic

/-- A local memory frame connecting two memory maps `after` and `before`. -/
private meta structure LocalMemFrame where
  /-- Proof term `f`. -/
  proof : Expr
  /-- Type of `f` after instantiating metavariables. -/
  type : Expr
  /-- Kind of frame: `0` = func eq `m' = m`, `1` = `Set.EqOn`, `2` = quantified `∀ ..., m' _ = m _`,
  `3` = `Modifies writes before after`. -/
  kind : ℕ

/-- Detect whether `ty` mentions `Data.mem` equality, raw `ℕ → ℕ` equality, `Set.EqOn`, `Modifies`,
or a pointwise/quantified equality between function applications `f a = g a`. -/
private meta def classifyMemFrame? (ty : Expr) : MetaM (Option ℕ) := do
  let ty := ty.cleanupAnnotations
  if let some (t, _, _) := ty.eq? then
    let tw ← whnfR t
    if tw.isForall then
      if tw.bindingDomain!.isConstOf ``Nat && tw.bindingBody!.isConstOf ``Nat then
        return some 0
    if tw.isConstOf ``Nat then
      return some 2
    return none
  if ty.isAppOfArity ``Set.EqOn 5 then
    return some 1
  if ty.isAppOfArity ``Modifies 3 then
    return some 3
  if ty.isForall then
    let body := ty.getForallBody.cleanupAnnotations
    if let some (t, lhs, rhs) := body.eq? then
      if (← whnfR t).isConstOf ``Nat then
        if lhs.isApp && rhs.isApp && !lhs.isAppOf ``Data.regs && !rhs.isAppOf ``Data.regs then
          return some 2
  return none

/-- Collect candidate memory frames from the local context. -/
private meta def collectMemFrames : MetaM (Array LocalMemFrame) := do
  let mut out : Array LocalMemFrame := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some k ← classifyMemFrame? ty then
      out := out.push { proof := d.toExpr, type := ty, kind := k }
  return out

/-- Is `c` a `Prop`-valued `structure` (excluding `Iff` and typeclasses)? -/
private meta def isPropStruct (c : Name) : MetaM Bool := do
  let env ← getEnv
  if c == ``Iff || c == ``And then return false
  if !isStructure env c || isClass env c then return false
  let some info := env.find? c | return false
  return info.type.getForallBody.isProp

/-- Try to prove a small side-condition goal `p` (`a < Db`, `k ≤ 10`, `k ≠ 5`, `a ∈ Set.Iio n`,
`a ∈ b.footprint`, etc.) using `assumption`, `rfl`, `decide`, `omega`, `simp + omega`, or silent
`@[wram_arith]` unfolding. -/
private meta def proveSideCond? (p : Expr) (finVars : Array Expr) : MetaM (Option Expr) := do
  let m ← mkFreshExprSyntheticOpaqueMVar p
  let g := m.mvarId!
  let saved ← saveState
  try
    let mut g' := g
    for fv in finVars do
      let fty ← whnfR (← inferType fv)
      if fty.isAppOfArity ``Fin 1 then
        let isLt ← mkAppM ``Fin.isLt #[fv]
        let (_, ng) ← g'.note (← mkFreshUserName `hfin) isLt
        g' := ng
    let ok ← g'.withContext do
      let tac ← `(tactic| first
        | assumption
        | rfl
        | decide
        | omega
        | (simp only [Block.mem_footprint, Block.Owns, Finset.mem_union,
            Finset.mem_singleton, Set.mem_Iio, Set.mem_Iic, Set.mem_Ioi, Set.mem_Ici, Set.mem_Ico,
            Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
            Set.mem_compl_iff, not_and, not_lt, not_le, Nat.add_zero, Nat.zero_add,
            Fin.val_mk, Fin.val_natCast, Data.set_mem, Data.set_regs,
            Data.write_regs] at *; first | omega | decide | wram_omega_silent))
      let saved2 ← saveState
      try
        let rem ← Term.TermElabM.run' <| Tactic.run g' (evalTactic tac)
        if rem.isEmpty then return true
        saved2.restore
      catch _ =>
        saved2.restore
      Cslib.Tactic.WramOmega.tryProve g'
    if ok then
      return some (← instantiateMVars m)
    saved.restore
    return none
  catch _ =>
    saved.restore
    return none

/-- Gather local `Fin _` free variables. -/
private meta def localFinVars : MetaM (Array Expr) := do
  let mut xs : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``Fin 1 then
      xs := xs.push d.toExpr
  return xs

/-- Try to instantiate a memory frame `mf` to produce a proof of `e = rhs` for a `ℕ`-valued
memory read `e` (`m' addr`). -/
private meta def applyMemFrame? (mf : LocalMemFrame) (e : Expr) (finVars : Array Expr) :
    MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  match mf.kind with
  | 0 =>
    let some (_, lhs, rhs) := mf.type.eq? | return none
    let .app fn arg := e | return none
    if ← withReducible (isDefEq fn lhs) then
      let pf ← mkCongrFun mf.proof arg
      return some (mkApp rhs arg, pf)
    return none
  | 1 =>
    let args := mf.type.getAppArgs
    let m' := args[2]!
    let m := args[3]!
    let .app fn arg := e | return none
    unless ← withReducible (isDefEq fn m') do return none
    let sideTy ← mkAppM ``Membership.mem #[args[4]!, arg]
    let some hp ← proveSideCond? sideTy finVars | return none
    let pf := mkApp2 mf.proof arg hp
    return some (mkApp m arg, pf)
  | 3 =>
    let args := mf.type.getAppArgs
    let writes := args[0]!
    let before := args[1]!
    let after := args[2]!
    let .app fn arg := e | return none
    unless ← withReducible (isDefEq fn after) do return none
    let sideTy := mkNot (← mkAppM ``Membership.mem #[writes, arg])
    let some hp ← proveSideCond? sideTy finVars | return none
    let pf := mkApp2 mf.proof arg hp
    return some (mkApp before arg, pf)
  | _ =>
    withNewMCtxDepth do
      let (xs, _, body) ← forallMetaTelescopeReducing mf.type
      let some (_, lhs, rhs) := body.eq? | return none
      let matched ← withReducible (isDefEq lhs e)
      if matched then
        let mut ok := true
        for x in xs do
          let x' ← instantiateMVars x
          unless x'.isMVar do continue
          let ty ← instantiateMVars (← inferType x')
          if ← isProp ty then
            let some hp ← proveSideCond? ty finVars | do ok := false; break
            x'.mvarId!.assign hp
          else
            ok := false; break
        if ok then
          let rhs' ← instantiateMVars rhs
          let lhs' ← instantiateMVars lhs
          if rhs' == lhs' then return none
          let pf ← instantiateMVars (mkAppN mf.proof xs)
          return some (rhs', ← mkExpectedTypeHint pf (← mkEq e rhs'))
      -- Special case: `lhs` is `m' (base + k)` and `e` is `m' base` (`k = 0`, `Nat.add_zero`).
      let .app lfn larg := lhs | return none
      let .app efn earg := e | return none
      unless lfn.isApp || lfn.isFVar || lfn.isConst do return none
      if larg.isAppOfArity ``HAdd.hAdd 6 then
        let base := larg.getArg! 4
        let k := larg.getArg! 5
        if k.isMVar && (← withReducible (isDefEq lfn efn)) &&
            (← withReducible (isDefEq base earg)) then
          k.mvarId!.assign (mkNatLit 0)
          let mut ok := true
          for x in xs do
            let x' ← instantiateMVars x
            unless x'.isMVar do continue
            let ty ← instantiateMVars (← inferType x')
            if ← isProp ty then
              let some hp ← proveSideCond? ty finVars | do ok := false; break
              x'.mvarId!.assign hp
            else
              ok := false; break
          if ok then
            let pfRaw ← instantiateMVars (mkAppN mf.proof xs)
            let .app rfn _ := (← instantiateMVars rhs) | return none
            let lhsZero ← mkAppM ``Nat.add_zero #[earg]
            let p1 ← mkCongrArg efn (← mkEqSymm lhsZero)
            let p3 ← mkCongrArg rfn lhsZero
            let pf ← mkEqTrans p1 (← mkEqTrans pfRaw p3)
            return some (mkApp rfn earg, pf)
      return none

/-- Rewrite one memory-read expression `m' addr` using `frames`. -/
private meta def memRewriteStep (frames : Array LocalMemFrame) (finVars : Array Expr) (e : Expr) :
    SimpM Simp.Step := do
  let .app fn _ := e | return .continue
  if e.isAppOf ``Data.regs || e.isAppOf ``HAdd.hAdd || e.isAppOf ``HMul.hMul ||
      e.isAppOf ``HSub.hSub || e.isAppOf ``HDiv.hDiv || e.isAppOf ``HMod.hMod ||
      fn.isAppOf ``OfNat.ofNat then
    return .continue
  for mf in frames do
    if let some (rhs, pf) ← applyMemFrame? mf e finVars then
      return .done { expr := rhs, proof? := some pf }
  return .continue

/-- Rewrite every memory read inside the target of `g` along local memory frames. -/
private meta def rewriteMemReads (g : MVarId) (frames : Array LocalMemFrame) : MetaM MVarId :=
  g.withContext do
    if frames.isEmpty then return g
    let finVars ← localFinVars
    let tgt ← instantiateMVars (← g.getType)
    let ctx ← Simp.mkContext (config := { maxSteps := 20000 })
      (congrTheorems := ← getSimpCongrTheorems)
    let (res, _) ← Simp.main tgt ctx (methods := { pre := memRewriteStep frames finVars })
    applySimpResultToTarget g tgt res

/-- Try closing a `Block.Realizes` / `Block.HoldsList` / `HeapAssertion.holds` goal from `h`
using `ram_keep` and/or local `Data.set` / `Data.write` / `Set.EqOn` / `Modifies` / quantified
frames. -/
private meta def tryKeepView (g : MVarId) (h : Expr) (frames : Array LocalMemFrame) :
    MetaM Bool :=
  g.withContext do
    let ht := (← instantiateMVars (← g.getType)).cleanupAnnotations
    let hty := (← instantiateMVars (← inferType h)).cleanupAnnotations
    let isView := ht.isAppOf ``Block.Realizes || ht.isAppOf ``Block.HoldsList ||
      ht.isAppOf ``HeapAssertion.holds
    unless isView do return false
    -- Fast multi-hop path via `MemFrame.tryProve` on `Set.EqOn after before (Set.Ico ...)`:
    let savedMf ← saveState
    try
      if ht.isAppOfArity ``Block.Realizes 3 && hty.isAppOfArity ``Block.Realizes 3 then
        let b := ht.getArg! 0
        let after := ht.getArg! 1
        let before := hty.getArg! 1
        let base ← mkAppM ``Block.base #[b]
        let len ← mkAppM ``Block.length #[b]
        let hi ← mkAppM ``HAdd.hAdd #[base, len]
        let reads ← mkAppM ``Set.Ico #[base, hi]
        let eqOnTy ← mkAppM ``Set.EqOn #[after, before, reads]
        let mEq ← mkFreshExprSyntheticOpaqueMVar eqOnTy
        if ← MemFrame.tryProve mEq.mvarId! then
          let sub ← mkAppOptM ``Set.Subset.rfl #[none, some reads]
          let pf ← mkAppM ``Block.Realizes.keep #[h, mEq, sub]
          g.assign (← mkExpectedTypeHint pf ht)
          return true
      else if ht.isAppOfArity ``Block.HoldsList 3 && hty.isAppOfArity ``Block.HoldsList 3 then
        let base := ht.getArg! 0
        let xs := ht.getArg! 1
        let after := ht.getArg! 2
        let before := hty.getArg! 2
        let len ← mkAppM ``List.length #[xs]
        let hi ← mkAppM ``HAdd.hAdd #[base, len]
        let reads ← mkAppM ``Set.Ico #[base, hi]
        let eqOnTy ← mkAppM ``Set.EqOn #[after, before, reads]
        let mEq ← mkFreshExprSyntheticOpaqueMVar eqOnTy
        if ← MemFrame.tryProve mEq.mvarId! then
          let sub ← mkAppOptM ``Set.Subset.rfl #[none, some reads]
          let pf ← mkAppM ``Block.HoldsList.keep #[h, mEq, sub]
          g.assign (← mkExpectedTypeHint pf ht)
          return true
    catch _ => pure ()
    savedMf.restore
    let saved ← saveState
    try
      let hn ← mkFreshUserName `sfView
      let (fvarId, g1) ← g.note hn h
      let id := mkIdent ((← g1.getDecl).lctx.get! fvarId).userName
      let ok ← g1.withContext do
        try
          let rem ← Term.TermElabM.run' <| Tactic.run g1 do
            evalTactic (← `(tactic| (
              try dsimp only [Cslib.WordRAM.Data.set_mem, Cslib.WordRAM.Data.write_mem]
              ram_keep $id)))
          return rem.isEmpty
        catch _ => return false
      if ok then return true
    catch _ => pure ()
    saved.restore
    for mf in frames do
      let saved2 ← saveState
      try
        let hIdent ← mkFreshUserName `sfView
        let (vfv, g1) ← g.note hIdent h
        let mIdent ← mkFreshUserName `sfMem
        let (mfv, g2) ← g1.note mIdent mf.proof
        let vid := mkIdent ((← g2.getDecl).lctx.get! vfv).userName
        let mid := mkIdent ((← g2.getDecl).lctx.get! mfv).userName
        let ok ← g2.withContext do
          try
            let rem ← Term.TermElabM.run' <| Tactic.run g2 do
              if mf.kind == 0 then
                evalTactic (← `(tactic| (rw [$mid:term]; exact $vid)))
              else if mf.kind == 1 then
                evalTactic (← `(tactic| first
                  | exact Cslib.WordRAM.Block.HoldsList.keep $vid $mid (by
                      intro a ha
                      simp only [Set.mem_Ico, Set.mem_Iio, Set.mem_Ici,
                        List.length_map, List.length_reverse, List.length_nil,
                        List.length_cons] at ha ⊢
                      first | omega | wram_omega_silent)
                  | exact Cslib.WordRAM.Block.Realizes.keep $vid $mid (by
                      intro a ha
                      simp only [Set.mem_Ico, Set.mem_Iio, Set.mem_Ici] at ha ⊢
                      first | omega | wram_omega_silent)
                  | exact Cslib.WordRAM.HeapAssertion.keep $vid $mid (by
                      intro a ha
                      simp only [Finset.mem_coe, Block.mem_footprint, Block.Owns,
                        Set.mem_Ico, Set.mem_Iio, Set.mem_Ici] at ha ⊢
                      first | omega | wram_omega_silent)))
              else if mf.kind == 3 then
                evalTactic (← `(tactic| (
                  have hModFn : ∀ a, a ∉ _ → _ := $mid
                  ram_keep $vid using hModFn)))
              else
                evalTactic (← `(tactic| ram_keep $vid using $mid))
            return rem.isEmpty
          catch _ => return false
        if ok then return true
      catch _ => pure ()
      saved2.restore
    return false

/-- Try running `tac` inside `MetaM` against `g`. Returns `true` iff `g` is solved. -/
private meta def tryTacticClose (g : MVarId) (tac : TacticM Unit) : MetaM Bool := do
  let saved ← saveState
  try
    let rem ← Term.TermElabM.run' <| Tactic.run g tac
    if rem.isEmpty then return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

/-- Unfold one transparent non-structure definition head on an expression when `tgt` and `hty`
have the same constant head (e.g. `HeaderConstsRep`, `PartialAt`, `Instances.Output`). -/
private meta def unfoldSameHead? (tgt hty : Expr) : MetaM (Option (Expr × Expr)) := do
  let .const c₁ _ := tgt.getAppFn | return none
  let .const c₂ _ := hty.getAppFn | return none
  if c₁ != c₂ then return none
  if c₁ == ``And || c₁ == ``Eq || c₁ == ``Iff || c₁ == ``Block.Realizes ||
      c₁ == ``Block.HoldsList || c₁ == ``HeapAssertion.holds then
    return none
  if ← isPropStruct c₁ then return none
  let env ← getEnv
  let some (.defnInfo _) := env.find? c₁ | return none
  let some tgt' ← unfoldDefinition? tgt | return none
  let some hty' ← unfoldDefinition? hty | return none
  return some (tgt', hty')

/-- Recursively add non-quantified field facts from `h : ty` to the local context of `g` so that
`omega`, `regs_frame`, and `mem_frame` automatically see bounds like `h.clauses_le`,
`h.stored_le`, `h.span`, and `h.heap_eq`. Returns updated `MVarId`. -/
private meta partial def exposeAuxFacts (g : MVarId) (h ty : Expr) (depth : ℕ := 0) :
    MetaM MVarId := do
  if depth ≥ 2 then return g
  let ty := ty.cleanupAnnotations
  if let some (p, q) := ty.and? then
    let g1 ← exposeAuxFacts g (mkApp3 (mkConst ``And.left) p q h) p depth
    return ← exposeAuxFacts g1 (mkApp3 (mkConst ``And.right) p q h) q depth
  let .const c _ := ty.getAppFn | return g
  if ← isPropStruct c then
    let env ← getEnv
    let mut cur := g
    for field in getStructureFields env c do
      let some proj := getProjFnForField? env c field | continue
      let p ← cur.withContext <| mkAppOptM proj ((ty.getAppArgs.map some).push (some h))
      let pty ← cur.withContext <| inferType p
      if pty.isAppOf ``LE.le || pty.isAppOf ``LT.lt || pty.isAppOf ``Eq then
        let (_, ng) ← cur.note (← mkFreshUserName `sfFact) p
        cur := ng
    return cur
  if let some (.defnInfo _) := (← getEnv).find? c then
    if depth == 0 && c != ``Block.Realizes && c != ``Block.HoldsList &&
        c != ``HeapAssertion.holds then
      if let some ty' ← unfoldDefinition? ty then
        return ← exposeAuxFacts g (← mkExpectedTypeHint h ty') ty' (depth + 1)
  if ty.isAppOf ``LE.le || ty.isAppOf ``LT.lt || ty.isAppOf ``Eq then
    let (_, ng) ← g.note (← mkFreshUserName `sfFact) h
    return ng
  return g

/-- Core recursive worker pairing goal `g` with witness `h : hty` (already sharing any outer
universal binders). Returns any subgoals that could not be closed automatically. -/
private meta partial def frameField (g : MVarId) (h : Expr) (depth : ℕ := 0) :
    MetaM (Array MVarId) := g.withContext do
  let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let hty := (← instantiateMVars (← inferType h)).cleanupAnnotations
  -- 0. Zeta-reduce `let` expressions sitting directly on the head of `tgt` or `hty`.
  if tgt.isLet || hty.isLet then
    let tgt' ← zetaReduce tgt
    let hty' ← zetaReduce hty
    let g' ← g.change tgt'
    let h' ← mkExpectedTypeHint h hty'
    return ← frameField g' h' depth
  -- 1. Already definitionally equal (`exact h`).
  if ← isDefEq tgt hty then
    g.assign h
    return #[]
  -- 2. Split matching `Prop`-valued `structure`.
  if let .const c _ := tgt.getAppFn then
    if let .const c' _ := hty.getAppFn then
      if c == c' && (← isPropStruct c) then
        let env ← getEnv
        let fields := getStructureFields env c
        let gs ← g.constructor
        let args := hty.getAppArgs.map some
        let mut rem : Array MVarId := #[]
        for i in [:gs.length] do
          let gi := gs[i]!
          if hlt : i < fields.size then
            let some proj := getProjFnForField? env c fields[i] | do
              rem := rem.push gi
              continue
            let hi ← gi.withContext <| mkAppOptM proj (args.push (some h))
            rem := rem ++ (← frameField gi hi (depth + 1))
          else
            rem := rem.push gi
        return rem
  -- 3. Split matching conjunction `And`.
  if let some (_, _) := tgt.and? then
    if let some (hp, hq) := hty.and? then
      let gs ← g.constructor
      if gs.length == 2 then
        let hl := mkApp3 (mkConst ``And.left) hp hq h
        let hr := mkApp3 (mkConst ``And.right) hp hq h
        let r1 ← frameField gs[0]! hl depth
        let r2 ← frameField gs[1]! hr depth
        return r1 ++ r2
  -- 4. Pure `rfl` (handles e.g. self-frame tail `∀ a, ... → z.mem a = z.mem a`).
  if ← tryTacticClose g (evalTactic (← `(tactic| (intros; rfl)))) then
    return #[]
  -- 5. Register equation via `RegsFrame.tryProve`, `wram_simp`, or `z.regs = y.regs`.
  if let some (_, lhs, _) := tgt.eq? then
    if lhs.isAppOf ``Data.regs then
      let savedReg ← saveState
      let okRegs ← do
        let (_, g1) ← g.note (← mkFreshUserName `sfReg) h
        RegsFrame.tryProve g1
      if okRegs then return #[]
      savedReg.restore
      let savedWram ← saveState
      let okWram ← g.withContext do
        let hn ← mkFreshUserName `sfReg
        let (fv, g1) ← g.note hn h
        let id := mkIdent ((← g1.getDecl).lctx.get! fv).userName
        tryTacticClose g1 (do
          evalTactic (← `(tactic| first
            | (rw [Cslib.WordRAM.Data.set_regs]; exact $id)
            | (wram_simp; try exact $id; try rfl))))
      if okWram then return #[]
      savedWram.restore
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let dty ← instantiateMVars d.type
        if let some (_, rl, _) := dty.eq? then
          if (← inferType rl).isForall then
            let savedEq ← saveState
            let idH ← mkFreshUserName `sfH
            let (hfv, g1) ← g.note idH h
            let hid := mkIdent ((← g1.getDecl).lctx.get! hfv).userName
            let did := mkIdent d.userName
            let okEq ← tryTacticClose g1 (do
              evalTactic (← `(tactic| (rw [$did:term]; exact $hid))))
            if okEq then return #[]
            savedEq.restore
  -- 6. Try `Block.Realizes` / `Block.HoldsList` / `HeapAssertion.holds` via `ram_keep`.
  let frames ← collectMemFrames
  if ← tryKeepView g h frames then
    return #[]
  -- 7. Quantified binder (`∀ x, ...`): peel 1-to-1 when `hty` is also a `∀`.
  if tgt.isForall && hty.isForall then
    if ← isDefEq tgt.bindingDomain! hty.bindingDomain! then
      let (fv, g1) ← g.intro1P
      let r ← g1.withContext do
        let hNext := mkApp h (mkFVar fv)
        frameField g1 hNext depth
      return r
  -- 8. Try `MemFrame.tryProve` with `h` in context (handles multi-hop frames, `Modifies`,
  -- `Data.havoc`, `Exec.mem_eq`, `@[wram_arith]` layout bounds, and nested reads `some (m a)`).
  if !tgt.isAppOf ``Block.Realizes && !tgt.isAppOf ``Block.HoldsList &&
      !tgt.isAppOf ``HeapAssertion.holds then
    let savedMem ← saveState
    let okMem ← do
      let (_, g1) ← g.note (← mkFreshUserName `sfPrev) h
      MemFrame.tryProve g1
    if okMem then return #[]
    savedMem.restore
  -- 9. Try direct `wram_simp` memory/update normalization against `h`.
  let saved8 ← saveState
  let okWramMem ← do
    let mut g0 := g
    for fv in ← localFinVars do
      let isLt ← mkAppM ``Fin.isLt #[fv]
      let (_, ng) ← g0.note (← mkFreshUserName `hfin) isLt
      g0 := ng
    let hn ← mkFreshUserName `sfPrev
    let (fv, g1) ← g0.note hn h
    let id := mkIdent ((← g1.getDecl).lctx.get! fv).userName
    tryTacticClose g1 (do
      evalTactic (← `(tactic| (
        try wram_simp
        try exact $id))))
  if okWramMem then return #[]
  saved8.restore
  -- 10. Rewrite every memory read in `tgt` along local memory frames, then close with `exact h`.
  let saved9 ← saveState
  let gRw ← rewriteMemReads g frames
  if ← gRw.withContext (isDefEq (← gRw.getType) hty) then
    gRw.assign h
    return #[]
  if ← gRw.withContext (do
      let hn ← mkFreshUserName `sfPrev
      let (fv, g1) ← gRw.note hn h
      let id := mkIdent ((← g1.getDecl).lctx.get! fv).userName
      tryTacticClose g1 (evalTactic (← `(tactic|
        first | exact $id | (simp only [Nat.add_zero]; exact $id))))) then
    return #[]
  saved9.restore
  -- 11. Unfold a transparent non-structure definition shared by `tgt` and `hty` (`PartialAt`,
  -- `HeaderConstsRep`, `TableSlotsRep`, `KeysValsRep`, `Instances.Output`, ...), once per depth.
  if depth < 8 then
    if let some (tgt', hty') ← unfoldSameHead? tgt hty then
      let g' ← g.change tgt'
      let h' ← mkExpectedTypeHint h hty'
      return ← frameField g' h' (depth + 1)
    if tgt.isAppOf ``Block.Realizes && hty.isAppOf ``Block.Realizes then
      let saved10 ← saveState
      if let (some tgt', some hty') := (← unfoldDefinition? tgt, ← unfoldDefinition? hty) then
        let g' ← g.change tgt'
        let h' ← mkExpectedTypeHint h hty'
        let rem ← frameField g' h' (depth + 1)
        if rem.isEmpty then return #[]
      saved10.restore
  -- 12. Leave remaining unsolved subgoal with `h` added to the context for convenient finishing.
  let (_, gOut) ← g.note (← mkFreshUserName `hprev) h
  return #[gOut]

/-- Find the latest local hypothesis whose head constant matches the goal's head constant. -/
private meta def findMatchingHyp? (tgt : Expr) : MetaM (Option Expr) := do
  let .const c _ := tgt.getAppFn | return none
  let mut found : Option Expr := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.getAppFn.isConstOf c then
      found := some d.toExpr
  return found

end StructFrame

/-- `struct_frame` transports a `Prop`-valued `structure` or conjunction predicate from a prior
state hypothesis `h : S … y` to the goal `S … z` by pairing fields 1-to-1:

* unchanged (`isDefEq`) and `rfl` fields (`Nodup`, `Fits`, bounds, self-frames) close immediately;
* register equations transfer through `regs_frame`, `wram_simp`, or `z.regs = y.regs`;
* `Block.Realizes`, `Block.HoldsList`, and `HeapAssertion.holds` transfer through `ram_keep`
  against `Data.write` updates, `Modifies`, `Set.EqOn`, or quantified memory frames;
* memory equations and quantified invariants (including transparent wrappers such as `PartialAt`
  and nested reads `s k = some (z.mem a)`) transfer through `mem_frame` and local memory-frame
  rewriting, checking arithmetic side conditions with `omega`, `decide`, and silent
  `@[wram_arith]` unfolding.

With no argument, `struct_frame` uses the most recent hypothesis with the same head constant as
the goal. Any field that cannot be discharged automatically is left as a focused subgoal with a
local `hprev` hypothesis holding the corresponding field of `h`. -/
syntax (name := structFrame) "struct_frame" (ppSpace term:max)? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| struct_frame $[$h?]?) => withMainContext do
    recordExtraModUse (isMeta := false) `Init.Omega
    let g0 ← getMainGoal
    let tgt ← instantiateMVars (← g0.getType)
    let hExpr ← match h? with
      | some hTerm => Term.elabTerm hTerm none
      | none =>
        let some e ← StructFrame.findMatchingHyp? tgt
          | throwError "struct_frame: no hypothesis matches goal head{indentExpr tgt}"
        pure e
    let hTy ← instantiateMVars (← inferType hExpr)
    if let (.const c₁ _, .const c₂ _) := (tgt.cleanupAnnotations.getAppFn,
        hTy.cleanupAnnotations.getAppFn) then
      if c₁ == c₂ then
        let tgtArgs := tgt.cleanupAnnotations.getAppArgs
        let hArgs := hTy.cleanupAnnotations.getAppArgs
        let n := min tgtArgs.size hArgs.size
        for idx in [:n] do
          if idx + 1 < tgtArgs.size && tgtArgs[idx]!.hasExprMVar then
            discard <| isDefEq tgtArgs[idx]! hArgs[idx]!
    let g1 ← StructFrame.exposeAuxFacts g0 hExpr hTy
    let rem ← StructFrame.frameField g1 hExpr
    replaceMainGoal rem.toList

end Cslib.WordRAM

end
