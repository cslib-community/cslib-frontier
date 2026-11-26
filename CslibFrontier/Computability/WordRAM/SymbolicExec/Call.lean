/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Computability.WordRAM.SymbolicExec
public import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Continuing symbolic execution through routine contracts

The tactic `wram_call` consumes a routine specification at the current `WP` or `WP.Exact` goal.
Its continuation receives the returned state and complete postcondition, with the routine's
instruction allowance already added by `WP.seq`. Resume straight-line execution with `wram_exec`.
The routine's definition stays closed: correctness, safety conditions and its charge come from
the contract, not from symbolic execution of its body.

Accepted contract shapes:
* Fixed-time existential specification: `∃ y, ExecWithin w c x y T ∧ P y` (or `Exec` at `WP.Exact`).
* Time-indexed weakest precondition: `WP w c x Q'` (or `WP.Exact w c x Q'` at `WP.Exact`).
* Direct deterministic execution: `ExecWithin w c x y T` or `Exec w c x y T`, optionally paired with
  a postcondition conjunction (`ExecWithin … ∧ P` / `Exec … ∧ P`).

`wram_call` uses **witness-preserving** rules (`WP.of_spec'`, `WP.Exact.of_spec'`, `WP.mono'`,
`WP.Exact.mono'`), keeping a local `ExecWithin` / `Exec` witness in the continuation context so
`regs_frame` and `mem_frame` can automatically follow `he.regs_eq` and `he.mem_eq` across the call.

If the goal starts with a `Code.seq`, `wram_call` first checks whether the contract applies to the
whole sequence and otherwise automatically peels `.seq` via `WP.seq` / `WP.Exact.seq`.

If the contract term is a universally quantified specification (such as an induction hypothesis or
bare theorem name), `wram_call` instantiates its telescope against the goal and automatically
discharges its side premises (`regs_frame`, `wram_simp`, `fits`, `omega`, silent `wram_omega`,
`decide`, local `assumption`, and memory-equality transport along `d.mem = x.mem`). Any remaining
nontrivial premises are left as tagged subgoals after the continuation. Optional `[h₁, h₂, …]`
hints supply extra facts or simp lemmas to the discharger.

The renamed form applies `ExecWithin.rename_post` / `Exec.rename_post` and retains the caller's
outside-register frame. Its injectivity proof `hf : f.Injective` may be omitted when `f` is
provably injective from the local context, standard `Fin` embeddings, `Fin.val` arithmetic, or
`decide`. The word `renamed` is not reserved: importers may still use it as an identifier.

## Main results

* `WP.of_spec`, `WP.Exact.of_spec`: continue from a fixed-time existential routine contract.
* `WP.of_spec'`, `WP.Exact.of_spec'`: witness-preserving variants retaining `ExecWithin` / `Exec`.
* `WP.mono'`, `WP.Exact.mono'`: witness-preserving weakening of `WP` / `WP.Exact`.
* `WP.of_execWithin_eq`, `WP.Exact.of_exec_eq`, `WP.of_execWithin_wit`, `WP.Exact.of_exec_wit`,
  `WP.of_execWithin_and`, `WP.Exact.of_exec_and`: continuations from direct `ExecWithin` / `Exec`
  contracts.
* `ExecWithin.rename_post_of_exec`, `Exec.rename_post_of_exec`: renamed existential views of direct
  executions.
* `wram_call`: consume a proved routine contract without unfolding its program.
-/

public section

namespace Cslib.WordRAM

/-- Continue from a routine's complete postcondition at its given instruction allowance. -/
theorem WP.of_spec {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, ExecWithin w c x y T ∧ P y) (hQ : ∀ y, P y → Q y T) :
    WP w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.of_execWithin hy (hQ y hP)

/-- Continue from a routine's complete postcondition while retaining its `ExecWithin` witness
in context so `regs_frame` and `mem_frame` can use `hy.regs_eq` and `hy.mem_eq`. -/
theorem WP.of_spec' {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, ExecWithin w c x y T ∧ P y)
    (hQ : ∀ y, ExecWithin w c x y T → P y → Q y T) :
    WP w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.of_execWithin hy (hQ y hy hP)

/-- Weaken a `WP` postcondition while retaining its `ExecWithin` witness in context. -/
theorem WP.mono' {B : Basis} {r w : ℕ} {c : Code B r} {x : Data r}
    {Q Q' : Data r → ℕ → Prop} (h : WP w c x Q)
    (hQ : ∀ y T, ExecWithin w c x y T → Q y T → Q' y T) :
    WP w c x Q' := by
  obtain ⟨y, T, he, hq⟩ := h
  exact WP.of_execWithin he (hQ y T he hq)

/-- Continue from a direct `ExecWithin` contract while retaining `y' = y` and the witness. -/
theorem WP.of_execWithin_eq {B : Basis} {r w T : ℕ} {c : Code B r} {x y : Data r}
    {Q : Data r → ℕ → Prop} (h : ExecWithin w c x y T)
    (hQ : ∀ y', ExecWithin w c x y' T → y' = y → Q y' T) :
    WP w c x Q :=
  WP.of_execWithin h (hQ y h rfl)

/-- Continue from a direct `ExecWithin w c x y T ∧ P` pair while retaining the witness. -/
theorem WP.of_execWithin_and {B : Basis} {r w T : ℕ} {c : Code B r} {x y : Data r}
    {P : Prop} {Q : Data r → ℕ → Prop} (h : ExecWithin w c x y T ∧ P)
    (hQ : ExecWithin w c x y T → P → Q y T) :
    WP w c x Q :=
  WP.of_execWithin h.1 (hQ h.1 h.2)

/-- Continue from a routine's complete postcondition at its exact instruction count. -/
theorem WP.Exact.of_spec {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, Exec w c x y T ∧ P y) (hQ : ∀ y, P y → Q y T) :
    WP.Exact w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.Exact.of_exec hy (hQ y hP)

/-- Continue from a routine's complete postcondition at its exact instruction count, retaining
its `Exec` witness so `regs_frame` and `mem_frame` can use `hy.regs_eq` and `hy.mem_eq`. -/
theorem WP.Exact.of_spec' {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, Exec w c x y T ∧ P y)
    (hQ : ∀ y, Exec w c x y T → P y → Q y T) :
    WP.Exact w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.Exact.of_exec hy (hQ y hy hP)

/-- Weaken a `WP.Exact` postcondition while retaining its `Exec` witness in context. -/
theorem WP.Exact.mono' {B : Basis} {r w : ℕ} {c : Code B r} {x : Data r}
    {Q Q' : Data r → ℕ → Prop} (h : WP.Exact w c x Q)
    (hQ : ∀ y T, Exec w c x y T → Q y T → Q' y T) :
    WP.Exact w c x Q' := by
  obtain ⟨y, T, he, hq⟩ := h
  exact WP.Exact.of_exec he (hQ y T he hq)

/-- Continue from a direct `Exec` contract while retaining `y' = y` and the witness. -/
theorem WP.Exact.of_exec_eq {B : Basis} {r w T : ℕ} {c : Code B r} {x y : Data r}
    {Q : Data r → ℕ → Prop} (h : Exec w c x y T)
    (hQ : ∀ y', Exec w c x y' T → y' = y → Q y' T) :
    WP.Exact w c x Q :=
  WP.Exact.of_exec h (hQ y h rfl)

/-- Continue from a direct `Exec w c x y T ∧ P` pair while retaining the witness. -/
theorem WP.Exact.of_exec_and {B : Basis} {r w T : ℕ} {c : Code B r} {x y : Data r}
    {P : Prop} {Q : Data r → ℕ → Prop} (h : Exec w c x y T ∧ P)
    (hQ : Exec w c x y T → P → Q y T) :
    WP.Exact w c x Q :=
  WP.Exact.of_exec h.1 (hQ h.1 h.2)

/-- Renamed existential view of a direct `ExecWithin` execution. -/
theorem ExecWithin.rename_post_of_exec {B : Basis} {r s w t : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s} {y : Data r}
    (h : ExecWithin w c (x.comap f) y t) :
    ∃ z, ExecWithin w (c.rename f) x z t ∧ z.comap f = y ∧
      ∀ i, (∀ j, f j ≠ i) → z.regs i = x.regs i :=
  ExecWithin.rename_post (Q := (· = y)) hf ⟨y, h, rfl⟩

/-- Renamed existential view of a direct `Exec` execution. -/
theorem Exec.rename_post_of_exec {B : Basis} {r s w t : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s} {y : Data r}
    (h : Exec w c (x.comap f) y t) :
    ∃ z, Exec w (c.rename f) x z t ∧ z.comap f = y ∧
      ∀ i, (∀ j, f j ≠ i) → z.regs i = x.regs i :=
  Exec.rename_post (Q := (· = y)) hf ⟨y, h, rfl⟩

/-- `WP.of_execWithin` keeping `h` in context as an `ExecWithin` witness. -/
theorem WP.of_execWithin_wit {B : Basis} {r w T : ℕ} {c : Code B r} {x y : Data r}
    {Q : Data r → ℕ → Prop} (h : ExecWithin w c x y T)
    (hQ : ExecWithin w c x y T → Q y T) : WP w c x Q :=
  WP.of_execWithin h (hQ h)

/-- `WP.Exact.of_exec` keeping `h` in context as an `Exec` witness. -/
theorem WP.Exact.of_exec_wit {B : Basis} {r w T : ℕ} {c : Code B r} {x y : Data r}
    {Q : Data r → ℕ → Prop} (h : Exec w c x y T)
    (hQ : Exec w c x y T → Q y T) : WP.Exact w c x Q :=
  WP.Exact.of_exec h (hQ h)

/-- Apply a fixed-time, direct, or time-indexed routine contract and expose its continuation.
Only bank-view projections are normalized; the callee program remains closed. -/
syntax (name := wramCall) "wram_call " term:max " with" (ppSpace colGt rintroPat)+ : tactic

namespace WramCall

open Lean Meta Elab Tactic

/-- The error raised by `tac`, or `none` if it succeeds; the state is restored either way. -/
private meta def errorOf (tac : TSyntax `tactic) : TacticM (Option MessageData) := do
  let s ← saveState
  try withoutRecover (evalTactic tac); s.restore; return none
  catch ex => s.restore; return some ex.toMessageData

/-- The head constant of the contract `h`'s type, with that type for display, when `h` elaborates
on its own; the state is restored. -/
private meta def contractType (h : Term) : TacticM (Option (Name × MessageData)) := do
  let s ← saveState
  try
    let ty ← whnfR (← instantiateMVars (← inferType (← Tactic.elabTerm h none true)))
    let r := (ty.getAppFn.constName, ← addMessageContext (indentExpr ty))
    s.restore; return some r
  catch _ => s.restore; return none

/-- Why no rule of a `wram_call` form applies. `rules` gives, for the head of the goal (`WP` or
`WP.Exact`), a sentence saying which contracts the form accepts there and, for each head of the
contract's type, the rule that applies it; Lean's failure for the rule matching the contract names
the mismatch. -/
private meta def explain (h : Term) (rules : Name → Option (MessageData × List (Name × Syntax))) :
    TacticM MessageData := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some (expected, rs) := rules (← whnfR tgt).getAppFn.constName
    | return m!"wram_call: expected a goal `WP w c x Q` or `WP.Exact w c x Q`, which `wram_exec` \
        leaves at a routine, got{indentExpr tgt}"
  let head := m!"wram_call: the contract does not apply to the goal{indentExpr tgt}\n{expected}"
  let ty? ← contractType h
  let pick := match ty? with
    | some (n, _) => rs.lookup n
    | none => rs.head?.map (·.2)
  match pick, ty? with
  | some rule, _ =>
    let err ← errorOf ⟨rule⟩
    return m!"{head}{(err.map fun e => m!"\n{e}").getD m!""}"
  | none, some (_, ty) => return m!"{head}\nThe contract has type{ty}"
  | none, none => return head

/-- Refine the goal with the first of `tacs` that succeeds and run `cont`; if none succeeds,
explain the failure with `rules` (see `explain`). -/
meta def run (h : Term) (tacs : List (TSyntax `tactic)) (cont : TSyntax `tactic)
    (rules : Name → Option (MessageData × List (Name × Syntax))) : TacticM Unit := do
  let rec go : List (TSyntax `tactic) → TacticM Unit
    | [] => do throwError (← explain h rules)
    | tac :: tacs => do
      let s ← saveState
      try withoutRecover (evalTactic tac)
      catch _ => s.restore; go tacs
  go tacs
  evalTactic cont

/-- Introduce `pats` across a continuation where the witness `ExecWithin`/`Exec` sits after the
initial `witAfter` binders (`y` for `of_spec'`, `y T` for `mono'`, `0` for `of_execWithin_wit`).
The witness is introduced with an inaccessible name so it never shadows user variables while
staying visible to `regs_frame` and `mem_frame`. -/
meta def introWithWitness (witAfter : ℕ) (pats : TSyntaxArray `rintroPat) :
    TacticM Unit := do
  let pre := pats[:min witAfter pats.size].toArray
  let post := pats[min witAfter pats.size:].toArray
  for p in pre do
    evalTactic (← `(tactic| rintro $p))
  if pats.size ≥ witAfter then
    let g ← getMainGoal
    let tgt ← instantiateMVars (← g.getType)
    if tgt.isForall then
      let (_, g') ← g.intro (← mkFreshUserName `hexec)
      replaceMainGoal [g']
  unless post.isEmpty do
    evalTactic (← `(tactic| rintro $post*))
  evalTactic (← `(tactic|
    try simp only [Cslib.WordRAM.Data.comap_regs, Cslib.WordRAM.Data.comap_mem] at *))

/-- Whether `g`'s head target is `WP w (.seq c₁ c₂) x Q` or `WP.Exact w (.seq c₁ c₂) x Q`. -/
private meta def tryPeelSeq (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let tgt := (WP.Exec.headBetaAll (← instantiateMVars (← g.getType))).consumeMData
  let (exact, code) ←
    if tgt.isAppOfArity ``WP 6 then pure (false, tgt.getArg! 3)
    else if tgt.isAppOfArity ``WP.Exact 6 then pure (true, tgt.getArg! 3)
    else return none
  let code ← whnfR code
  unless code.isAppOfArity ``Code.seq 4 do return none
  let rule := if exact then ``WP.Exact.seq else ``WP.seq
  let g ← g.replaceTargetDefEq tgt
  let [g'] ← g.apply (← mkConstWithFreshMVarLevels rule) | return none
  return some g'

/-- Run `attempt` against the current goal, peeling leading `Code.seq` layers via `WP.seq` /
`WP.Exact.seq` only if the direct call fails. Restores the state on failure. -/
meta def withSeqPeel (attempt : TacticM Bool) : TacticM Bool := do
  let s0 ← saveState
  if ← attempt then return true
  s0.restore
  let mut cur := (← getMainGoal)
  for _ in [:8] do
    let some next ← tryPeelSeq cur | break
    replaceMainGoal [next]
    let s1 ← saveState
    if ← attempt then return true
    s1.restore
    cur := next
  s0.restore
  return false

/-- Rewrite every `s'.mem` expression back along `Data.set_mem`, `Data.comap_mem`,
`Data.extend_mem`, `Data.havoc_mem`, and local `memEqs` chains so memory invariants like
`TableRep … d.mem` or `HoldsList … d.mem` match hypotheses on `x.mem`. -/
private meta def rewriteMemTarget (F : RegsFrame.Facts) (g : MVarId) : MetaM MVarId :=
    g.withContext do
  if F.memEqs.isEmpty then
    let tgt ← instantiateMVars (← g.getType)
    unless (tgt.find? fun e =>
        e.isAppOf ``Data.set || e.isAppOf ``Data.comap || e.isAppOf ``Data.extend ||
          e.isAppOf `Cslib.WordRAM.Data.havoc).isSome do
      return g
  let hasHavocMem := (← getEnv).contains `Cslib.WordRAM.Data.havoc_mem
  let step : Simp.Simproc := fun e => do
    if e.isAppOfArity ``Data.mem 2 then
      let d := e.getArg! 1
      let r := e.getArg! 0
      if d.isAppOfArity ``Data.set 4 then
        let args := d.getAppArgs
        let pf := mkAppN (mkConst ``Data.set_mem) #[args[0]!, args[1]!, args[2]!, args[3]!]
        return .visit { expr := mkApp2 (mkConst ``Data.mem) r args[1]!, proof? := some pf }
      if d.isAppOfArity ``Data.comap 4 then
        let args := d.getAppArgs
        let pf := mkAppN (mkConst ``Data.comap_mem) #[args[0]!, args[1]!, args[2]!, args[3]!]
        return .visit { expr := mkApp2 (mkConst ``Data.mem) args[1]! args[3]!, proof? := some pf }
      if d.isAppOfArity ``Data.extend 5 then
        let args := d.getAppArgs
        let pf := mkAppN (mkConst ``Data.extend_mem)
          #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!]
        return .visit { expr := mkApp2 (mkConst ``Data.mem) args[0]! args[3]!, proof? := some pf }
      if hasHavocMem && d.isAppOfArity `Cslib.WordRAM.Data.havoc 6 then
        let args := d.getAppArgs
        let pf := mkAppN (mkConst `Cslib.WordRAM.Data.havoc_mem)
          #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!]
        return .visit { expr := args[5]!, proof? := some pf }
      if let some (sPrev, h) := F.memEqs[d]? then
        return .visit { expr := mkApp2 (mkConst ``Data.mem) r sPrev, proof? := some h }
    return .continue
  let tgt ← instantiateMVars (← g.getType)
  let ctx ← Simp.mkContext (config := { maxSteps := 4000 })
    (congrTheorems := ← getSimpCongrTheorems)
  let (res, _) ← Simp.main tgt ctx (methods := { pre := step })
  applySimpResultToTarget g tgt res

/-- Close `g` by `True.intro`, syntactic match against `hints` or local hypotheses, or reducible
`isDefEq` against non-forall local hypotheses / `apply` of hints. -/
private meta partial def closeByAssumeOrHint (hints : Array Expr) (g : MVarId) : MetaM Bool :=
    g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let tgtC := tgt.cleanupAnnotations
  if tgtC.isTrue then
    g.assign (mkConst ``True.intro); return true
  for h in hints do
    let hty ← instantiateMVars (← inferType h)
    if hty.cleanupAnnotations == tgtC then
      g.assign (← mkExpectedTypeHint h tgt); return true
  if let some h ← WP.Exec.assumption? tgt then
    g.assign h; return true
  for h in hints do
    let s ← saveState
    try
      if (← g.apply h).isEmpty then return true
    catch _ => pure ()
    s.restore
  for d? in (← getLCtx).decls.toArray.reverse do
    let some d := d? | continue
    if d.isImplementationDetail then continue
    let s ← saveState
    let dty ← instantiateMVars d.type
    if dty.isForall then continue
    if ← withReducible (isDefEq dty tgt) then
      g.assign d.toExpr
      return true
    s.restore
  return false

/-- Run `wram_simps` + `autoReadSimp` + user `hintStx` on `e`, building the simp context once per
call and running inside a single `withSimpContext` scope. -/
private meta def simpWithCallCtx (F : RegsFrame.Facts) (hintStx : Array Syntax)
    (k : (Expr → MetaM Simp.Result) → TacticM Bool) : TacticM Bool := do
  let extra ← `(Lean.Parser.Tactic.simpLemma| Cslib.WordRAM.Data.comap_regs)
  let extra2 ← `(Lean.Parser.Tactic.simpLemma| Cslib.WordRAM.Data.comap_mem)
  let extra3 ← `(Lean.Parser.Tactic.simpLemma| Matrix.cons_val_zero)
  let extra4 ← `(Lean.Parser.Tactic.simpLemma| Matrix.cons_val_one)
  let extra5 ← `(Lean.Parser.Tactic.simpLemma| Matrix.cons_val)
  let extra6 ← `(Lean.Parser.Tactic.simpLemma| Nat.zero_mul)
  let extra7 ← `(Lean.Parser.Tactic.simpLemma| Nat.mul_zero)
  let extra8 ← `(Lean.Parser.Tactic.simpLemma| Nat.one_mul)
  let extra9 ← `(Lean.Parser.Tactic.simpLemma| Nat.mul_one)
  let extra10 ← `(Lean.Parser.Tactic.simpLemma| Nat.pow_zero)
  let extra11 ← `(Lean.Parser.Tactic.simpLemma| Nat.shiftLeft_zero)
  let allStx := #[extra.raw, extra2.raw, extra3.raw, extra4.raw, extra5.raw,
    extra6.raw, extra7.raw, extra8.raw, extra9.raw, extra10.raw, extra11.raw] ++ hintStx
  let autoWram := wram.exec.autoWramOmega.get (← getOptions)
  let disch ← liftMacroM <| WP.Exec.dischOf none autoWram
  WP.Exec.withSimpContext disch allStx fun ctx simprocs d => do
    let chain (r1 r2 : Simp.Result) : MetaM Simp.Result := do
      match r1.proof?, r2.proof? with
      | none, none => return { expr := r2.expr }
      | some p1, none => return { expr := r2.expr, proof? := some p1 }
      | none, some p2 => return { expr := r2.expr, proof? := some p2 }
      | some p1, some p2 => return { expr := r2.expr, proof? := some (← mkEqTrans p1 p2) }
    let runSimp (e : Expr) : MetaM Simp.Result := do
      let r1 := (← Lean.Meta.simp e ctx simprocs (some d)).1
      let r2 ← RegsFrame.autoReadSimp F r1.expr
      if r2.expr == r1.expr && r2.proof?.isNone then return r1
      let r12 ← chain r1 r2
      let r3 := (← Lean.Meta.simp r12.expr ctx simprocs (some d)).1
      chain r12 r3
    k runSimp

/-- Fast `MetaM` `intros` + `Omega.omega` without tactic syntax elaboration overhead. -/
private meta def tryMetaOmega (g : MVarId) : MetaM Bool := do
  let saved ← saveState
  try
    let (_, g') ← g.intros
    let some gContra ← g'.falseOrByContra | return true
    gContra.withContext do
      let type ← gContra.getType
      let proof ← mkFreshExprSyntheticOpaqueMVar type
      let hyps ← getLocalHyps
      Omega.omega hyps.toList proof.mvarId!
      gContra.assign (← mkAuxTheorem type (← instantiateMVars proof) (zetaDelta := true))
    return true
  catch _ =>
    saved.restore
    return false

/-- Try to discharge one premise metavariable `m` via direct hypotheses, memory transport,
`regs_frame`, or `runSimp`. Instantiates open `rhs` mvars of register equations (`s.regs i = ?v`)
so `omega`/`fits` never guess values. -/
private meta def tryDischargeRegOrMem (F : RegsFrame.Facts) (hints : Array Expr)
    (hintStx : Array Syntax) (runSimp : Expr → MetaM Simp.Result) (m : MVarId) :
    TacticM Bool := do
  if ← m.isAssigned then return false
  let s ← saveState
  let ok ← m.withContext do
    let tgt ← instantiateMVars (← m.getType)
    unless ← isProp tgt do return false
    let hasMVar := tgt.hasExprMVar
    let mentionsMem := (tgt.find? (·.isAppOf ``Data.mem)).isSome
    if !hasMVar || mentionsMem then
      let mMem ← rewriteMemTarget F m
      if ← closeByAssumeOrHint hints mMem then return true
      s.restore
      let sConj ← saveState
      let mMem2 ← rewriteMemTarget F m
      let tgtMem ← instantiateMVars (← mMem2.getType)
      if (tgtMem.and?).isSome then
        if let some gs ← observing? mMem2.constructor then
          let mut allOk := true
          for sub in gs do
            unless ← closeByAssumeOrHint hints sub do
              allOk := false; break
          if allOk then return true
      sConj.restore
    if let some (_, lhs, rhs) := tgt.cleanupAnnotations.eq? then
      if (lhs.find? fun t => (RegsFrame.read? t).isSome).isSome then
        if ← RegsFrame.tryProve m (some F) then return true
        if !hintStx.isEmpty || (lhs.find? (·.isAppOf ``Data.comap)).isSome ||
            (lhs.find? (·.isAppOf ``Data.set)).isSome then
          let s1 ← saveState
          let closed ← try
            let rl ← runSimp lhs
            let lFinal := rl.expr
            if ← isDefEq lFinal rhs then
              let pf ← match rl.proof? with | some p => pure p | none => mkEqRefl lFinal
              m.assign (← mkExpectedTypeHint pf tgt)
              pure true
            else if !rhs.hasExprMVar then
              let rr ← runSimp rhs
              if ← isDefEq lFinal rr.expr then
                let pf ← match rl.proof?, rr.proof? with
                  | none, none => mkEqRefl lFinal
                  | some pl, none => pure pl
                  | none, some pr => mkEqSymm pr
                  | some pl, some pr => mkEqTrans pl (← mkEqSymm pr)
                m.assign (← mkExpectedTypeHint pf tgt)
                pure true
              else
                pure false
            else
              pure false
          catch _ => pure false
          if closed then return true
          s1.restore
    if !tgt.hasExprMVar then
      if ← RegsFrame.tryProve m (some F) then return true
    return false
  unless ok do s.restore
  return ok

/-- Full discharge attempt for a ground `Prop` premise `m` (no unresolved expr metavariables).
Runs at most once per premise after value metavariables have converged. -/
private meta partial def tryDischargeGround (F : RegsFrame.Facts) (hints : Array Expr)
    (hintStx : Array Syntax) (runSimp : Expr → MetaM Simp.Result) (alreadyCheckedRegMem : Bool)
    (m : MVarId) : TacticM Bool := do
  if ← m.isAssigned then return false
  let s ← saveState
  let tgt ← m.withContext <| instantiateMVars (← m.getType)
  unless ← m.withContext <| isProp tgt do return false
  if tgt.hasExprMVar then return false
  let tryFits (g : MVarId) : TacticM Bool := do
    let s1 ← saveState
    try
      let gs ← withoutRecover (evalTacticAt (← `(tactic| fits)) g)
      if gs.isEmpty then return true
      s1.restore; return false
    catch _ => s1.restore; return false
  -- 1. Reflexivity and closed `decide`.
  if (← m.withContext do
      try m.refl; return true catch _ => pure false) then return true
  if let some (some h) ← m.withContext <| WP.Exec.decideClosed? tgt then
    m.withContext <| m.assign (← mkExpectedTypeHint h tgt)
    return true
  -- 2. Direct hypothesis / hint / `regs_frame` match (only if not just run on this exact `tgt`).
  if !alreadyCheckedRegMem then
    if ← tryDischargeRegOrMem F hints hintStx runSimp m then return true
  -- 3. `fits` (gated strictly to `Fits _ _` goals).
  if tgt.cleanupAnnotations.isAppOf ``Fits then
    if ← tryFits m then return true
  -- 4. Fast `MetaM` `intros` + `omega`.
  if ← m.withContext <| tryMetaOmega m then return true
  -- 5. Silent, heartbeat-bounded `wram_omega`.
  if ← m.withContext <| Cslib.Tactic.WramOmega.tryProve m then return true
  -- 6. Quantified memory frame (`∀ i < N, s.mem … = …`): transport `s.mem` back and match hyp.
  if tgt.isForall then
    let sMem ← saveState
    let okMem ← try
      let m' ← rewriteMemTarget F m
      if ← closeByAssumeOrHint hints m' then pure true else do
        let (fvs, body) ← m'.intros
        if fvs.isEmpty then pure false else
          body.withContext do
            let b' ← rewriteMemTarget F body
            if ← closeByAssumeOrHint hints b' then return true
            for d? in (← getLCtx).decls.toArray.reverse do
              let some d := d? | continue
              if d.isImplementationDetail then continue
              let dt := (← instantiateMVars d.type).cleanupAnnotations
              if dt.isForall then
                let s2 ← saveState
                let applied? ← try
                  let rest ← b'.apply d.toExpr
                  if rest.isEmpty then pure true
                  else do
                    let mut allClosed := true
                    for r in rest do
                      let r' ← r.withContext <| instantiateMVars (← r.getType)
                      let okR ← if let some h ← r.withContext <| WP.Exec.assumption? r' then
                        r.assign h; pure true
                      else
                        r.withContext <| tryMetaOmega r
                      unless okR do allClosed := false; break
                    pure allClosed
                catch _ => pure false
                if applied? then return true
                s2.restore
            return false
    catch _ => pure false
    if okMem then return true
    sMem.restore
  -- 7. Simplify via cached `runSimp` when hints are given or `Data.*` / trivial arith ops appear,
  -- then close with `refl` / `assumption` / `fits` / `omega` / `wram_omega`.
  if !hintStx.isEmpty || (tgt.find? fun e =>
      e.isAppOf ``Data.regs || e.isAppOf ``Data.mem || e.isAppOf ``Data.comap ||
        e.isAppOf ``Data.extend || e.isAppOf `Cslib.WordRAM.Data.havoc ||
        e.isAppOf ``HPow.hPow || e.isAppOf ``HShiftLeft.hShiftLeft ||
        e.isAppOf ``HMul.hMul || e.isAppOf ``HAdd.hAdd).isSome then
    let sSimp ← saveState
    let okSimp ← try
      let (_, mBody) ← m.intros
      let bTgt ← mBody.withContext <| instantiateMVars (← mBody.getType)
      let res ← mBody.withContext <| runSimp bTgt
      let m' ← mBody.withContext <| applySimpResultToTarget mBody bTgt res
      let tgt' ← m'.withContext <| instantiateMVars (← m'.getType)
      if tgt'.cleanupAnnotations.isTrue then
        m'.assign (mkConst ``True.intro); pure true
      else if (← m'.withContext do try m'.refl; return true catch _ => pure false) then
        pure true
      else if ← closeByAssumeOrHint hints m' then
        pure true
      else if tgt'.cleanupAnnotations.isAppOf ``Fits && (← tryFits m') then
        pure true
      else if ← m'.withContext <| tryMetaOmega m' then
        pure true
      else if ← m'.withContext <| Cslib.Tactic.WramOmega.tryProve m' then
        pure true
      else
        pure false
    catch _ => pure false
    if okSimp then return true
    sSimp.restore
  -- 8. Structural hint application (`m.apply h`, e.g. `hfit_q.of_le …`).
  for h in hints do
    let s3 ← saveState
    let ok ← try
      let sub ← m.apply h
      if sub.isEmpty then pure true
      else do
        let mut good := true
        for sg in sub do
          if ← tryDischargeGround F #[] #[] runSimp false sg then continue
          good := false; break
        pure good
    catch _ => pure false
    if ok then return true
    s3.restore
  s.restore
  return false

/-- Discharge all resolvable `Prop` metavariables in `mvars`:
1. Fixpoint pass binding value metavariables via register equations and direct hypotheses/hints
   (caching failed target expressions so unchanged premises are not re-tested).
2. Single ground pass running arithmetic, `fits`, and `simp` dischargers once per remaining
   ground `Prop` premise. -/
meta def dischargePremises (mvars : Array MVarId) (hintTerms : Array Term) :
    TacticM (Array MVarId) := do
  if mvars.isEmpty then return #[]
  recordExtraModUse (isMeta := false) `Init.Omega
  let facts ← RegsFrame.scan
  let mut hintsAcc : Array Expr := #[]
  let mut hintStxAcc : Array Syntax := #[]
  for t in hintTerms do
    hintStxAcc := hintStxAcc.push (← `(Lean.Parser.Tactic.simpLemma| $t:term)).raw
    try
      let e ← Tactic.elabTerm t none false
      hintsAcc := hintsAcc.push (← instantiateMVars e)
    catch _ => pure ()
  let hints := hintsAcc
  let hintStx := hintStxAcc
  let _ ← simpWithCallCtx facts hintStx fun runSimp => do
    let mut lastFailed : Std.HashMap MVarId Expr := {}
    -- Phase 1: bind value metavariables (`s.regs i = ?v`) and match direct hypotheses.
    for _ in [:4] do
      let mut progress := false
      for m in mvars do
        if ← m.isAssignedOrDelayedAssigned then continue
        let curTgt ← m.withContext <| instantiateMVars (← m.getType)
        if lastFailed[m]? == some curTgt then continue
        if ← tryDischargeRegOrMem facts hints hintStx runSimp m then
          progress := true
        else
          lastFailed := lastFailed.insert m curTgt
      unless progress do break
    -- Phase 2: run ground discharger at most once per remaining ground `Prop` premise.
    for m in mvars do
      if ← m.isAssignedOrDelayedAssigned then continue
      let curTgt ← m.withContext <| instantiateMVars (← m.getType)
      let alreadyChecked := lastFailed[m]? == some curTgt
      discard <| tryDischargeGround facts hints hintStx runSimp alreadyChecked m
    return true
  let mut remaining : Array MVarId := #[]
  let mut seen : Std.HashSet MVarId := {}
  for m in mvars do
    if seen.contains m then continue
    seen := seen.insert m
    unless ← m.isAssignedOrDelayedAssigned do
      remaining := remaining.push m
  return remaining

/-- Collect unassigned metavariables introduced by elaborating `hTerm`, preserving binder order and
user names for tagging any leftover side goals. -/
private meta def applyAuto (mode : Name) (hTerm : Term) (hf? : Option Term)
    (hintTerms : Array Term) (pats? : Option (TSyntaxArray `rintroPat)) :
    TacticM Bool := withMainContext do
  let g ← getMainGoal
  let tgt := (WP.Exec.headBetaAll (← instantiateMVars (← g.getType))).consumeMData
  let exact ←
    if tgt.isAppOfArity ``WP 6 then pure false
    else if tgt.isAppOfArity ``WP.Exact 6 then pure true
    else return false
  let g ← g.replaceTargetDefEq tgt
  let targetCode := tgt.getArg! 3
  let hfExpr? : Option Expr ←
    if mode == `direct then pure none
    else do
      let codeR ← whnfR targetCode
      unless codeR.isAppOfArity ``Code.rename 5 do return false
      let f := codeR.getArg! 3
      match hf? with
      | some hfTerm =>
        let expectedTy ← mkAppM ``Function.Injective #[f]
        try
          let e ← Tactic.elabTermEnsuringType hfTerm (some expectedTy)
          pure (some e)
        catch _ => return false
      | none =>
        let some hf ← RegsFrame.proveBankInjective? f | return false
        pure (some hf)
  let (hExpr, holeMVars) ← do
    let s ← saveState
    try
      let e ← Tactic.elabTerm hTerm none true
      Term.synthesizeSyntheticMVars (postpone := .yes)
      let holes ← getMVars (← instantiateMVars e)
      pure (e, holes)
    catch _ =>
      s.restore
      return false
  let hTy ← whnfR (← instantiateMVars (← inferType hExpr))
  let (teleArgs, _, concl) ← forallMetaTelescope hTy
  let names ← forallTelescope hTy fun xs _ => xs.mapM (·.fvarId!.getUserName)
  for (arg, nm) in teleArgs.zip names do
    arg.mvarId!.setTag nm
  let hApp := mkAppN hExpr teleArgs
  let concl ← whnfR (← instantiateMVars concl)
  let conclHead := concl.getAppFn.constName?
  let hasPats := pats?.isSome
  let tryRule (ruleName : Name) (witAfter : ℕ) (wrapArg : Expr → MetaM Expr) :
      TacticM (Option (MVarId × ℕ)) := do
    let s ← saveState
    try
      let arg ← wrapArg hApp
      let c ← mkConstWithFreshMVarLevels ruleName
      let (rArgs, _, rConcl) ← forallMetaTelescope (← inferType c)
      unless ← isDefEq rConcl (← g.getType) do s.restore; return none
      let n := rArgs.size
      unless n ≥ 2 do s.restore; return none
      let argSlot := rArgs[n - 2]!
      let contSlot := rArgs[n - 1]!
      unless ← isDefEq (← inferType arg) (← inferType argSlot) do s.restore; return none
      unless ← isDefEq argSlot arg do s.restore; return none
      g.assign (← instantiateMVars (mkAppN c rArgs))
      return some (contSlot.mvarId!, witAfter)
    catch _ => s.restore; return none
  let applied? : Option (MVarId × ℕ) ←
    if mode == `direct then
      match exact, conclHead with
      | false, some ``Exists => tryRule ``WP.of_spec' 1 pure
      | false, some ``WP => tryRule ``WP.mono' 2 pure
      | false, some ``ExecWithin =>
        if hasPats then tryRule ``WP.of_execWithin_eq 1 pure
        else tryRule ``WP.of_execWithin_wit 0 pure
      | false, some ``And =>
        if hasPats then tryRule ``WP.of_execWithin_and 0 pure
        else
          tryRule ``WP.of_execWithin_wit 0 fun e => mkAppM ``And.left #[e]
      | true, some ``Exists => tryRule ``WP.Exact.of_spec' 1 pure
      | true, some ``WP.Exact => tryRule ``WP.Exact.mono' 2 pure
      | true, some ``Exec =>
        if hasPats then tryRule ``WP.Exact.of_exec_eq 1 pure
        else tryRule ``WP.Exact.of_exec_wit 0 pure
      | true, some ``And =>
        if hasPats then tryRule ``WP.Exact.of_exec_and 0 pure
        else
          tryRule ``WP.Exact.of_exec_wit 0 fun e => mkAppM ``And.left #[e]
      | _, _ => pure none
    else if mode == `renamed then
      let some hf := hfExpr? | return false
      let codeR ← whnfR targetCode
      let f := codeR.getArg! 3
      let targetX := tgt.getArg! 4
      let smallX ← mkAppM ``Data.comap #[f, targetX]
      let wrap (nm : Name) (e : Expr) : MetaM Expr := do
        let ety ← whnfR (← instantiateMVars (← inferType e))
        if ety.isAppOfArity ``Exists 2 then
          if let .lam vn yTy body bi := ety.getArg! 1 then
            if let some (exTerm, qBody) := body.and? then
              if exTerm.getAppNumArgs == 7 then
                let _ ← isDefEq (exTerm.getArg! 4) smallX
                let qLam := Expr.lam vn yTy (← instantiateMVars qBody) bi
                return ← mkAppOptM nm #[none, none, none, none, none, none, some hf,
                  none, some targetX, some qLam, some e]
        else if ety.getAppNumArgs == 7 then
          let _ ← isDefEq (ety.getArg! 4) smallX
        mkAppOptM nm #[none, none, none, none, none, none, some hf, none, some targetX,
          none, some e]
      match exact, conclHead with
      | false, some ``Exists => tryRule ``WP.of_spec' 1 (wrap ``ExecWithin.rename_post)
      | false, some ``ExecWithin => tryRule ``WP.of_spec' 1 (wrap ``ExecWithin.rename_post_of_exec)
      | true, some ``Exists => tryRule ``WP.Exact.of_spec' 1 (wrap ``Exec.rename_post)
      | true, some ``Exec => tryRule ``WP.Exact.of_spec' 1 (wrap ``Exec.rename_post_of_exec)
      | _, _ => pure none
    else
      pure none
  let some (contM, witAfter) := applied? | return false
  replaceMainGoal [contM]
  let mut allM : Array MVarId := #[]
  for a in holeMVars do
    unless a == contM do allM := allM.push a
  for a in teleArgs do
    let mid := a.mvarId!
    unless mid == contM do allM := allM.push mid
  let leftover ← withMainContext <| dischargePremises allM hintTerms
  let contTy ← contM.withContext <| instantiateMVars (← contM.getType)
  let contM ← contM.replaceTargetDefEq (WP.Exec.headBetaAll contTy)
  replaceMainGoal [contM]
  match pats? with
  | some pats =>
    introWithWitness witAfter pats
  | none =>
    let gCont ← getMainGoal
    let tgtC ← instantiateMVars (← gCont.getType)
    if tgtC.isForall then
      let (_, g') ← gCont.intro (← mkFreshUserName `hexec)
      replaceMainGoal [g']
    evalTactic (← `(tactic|
      try simp only [Cslib.WordRAM.Data.comap_regs, Cslib.WordRAM.Data.comap_mem] at *))
  let contGoals ← getGoals
  setGoals (contGoals ++ leftover.toList)
  pruneSolvedGoals
  return true

/-- Check whether `hTerm` elaborates to a quantified `∀` (needing telescope/auto-discharge),
contains unfilled `_` holes, or is a direct `ExecWithin` / `Exec` / `And` contract. -/
private meta def needsAuto (hTerm : Term) : TacticM Bool := withMainContext do
  let s ← saveState
  try
    let e ← Tactic.elabTerm hTerm none true
    let ty ← whnfR (← instantiateMVars (← inferType e))
    let hasHoles := !(← getMVars e).isEmpty
    let r := ty.isForall || hasHoles ||
      ty.isAppOf ``ExecWithin || ty.isAppOf ``Exec || ty.isAppOf ``And
    s.restore
    return r
  catch _ =>
    s.restore
    return false

end WramCall

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_call $h with $pats*) => do
    let runLegacy : TacticM Bool := do
      let ofSpec ← `(tactic| refine Cslib.WordRAM.WP.of_spec' $h ?_)
      let mono ← `(tactic| refine Cslib.WordRAM.WP.mono' $h ?_)
      let exactOfSpec ← `(tactic| refine Cslib.WordRAM.WP.Exact.of_spec' $h ?_)
      let exactMono ← `(tactic| refine Cslib.WordRAM.WP.Exact.mono' $h ?_)
      for (tac, witAfter) in [(ofSpec, 1), (mono, 2), (exactOfSpec, 1), (exactMono, 2)] do
        let s ← saveState
        try
          withoutRecover (evalTactic tac)
          WramCall.introWithWitness witAfter pats
          return true
        catch _ => s.restore
      return false
    if ← WramCall.withSeqPeel runLegacy then return
    if ← WramCall.needsAuto h then
      if ← WramCall.withSeqPeel (WramCall.applyAuto `direct h none #[] (some pats)) then
        return
    let ofSpec ← `(tactic| refine Cslib.WordRAM.WP.of_spec $h ?_)
    let mono ← `(tactic| refine Cslib.WordRAM.WP.mono $h ?_)
    let exactOfSpec ← `(tactic| refine Cslib.WordRAM.WP.Exact.of_spec $h ?_)
    let exactMono ← `(tactic| refine Cslib.WordRAM.WP.Exact.mono $h ?_)
    WramCall.run h [ofSpec, mono, exactOfSpec, exactMono]
      (← `(tactic| rintro $pats*))
      fun
      | ``WP => some (m!"The contract must have type `∃ y, ExecWithin w c x y T ∧ P y` or \
          `WP w c x Q'`.",
          [(``Exists, ofSpec), (``WP, mono)])
      | ``WP.Exact => some (m!"The contract must have type `∃ y, Exec w c x y T ∧ P y` or \
          `WP.Exact w c x Q'`.",
          [(``Exists, exactOfSpec), (``WP.Exact, exactMono)])
      | _ => none

/-- Direct `wram_call h` without `with` (for bare `ExecWithin` / `Exec` contracts), optional hint
lemmas `[h₁, …]`, and `renamed` bank forms. -/
tactic_extension wramCall

@[tactic_alt wramCall]
syntax (name := wramCallDirect) (priority := low) "wram_call " term:max
  (ppSpace colGt "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wram_call $h $[[$hints,*]]?) => do
    let hs := (hints.map (·.getElems)).getD #[]
    if ← WramCall.withSeqPeel (WramCall.applyAuto `direct h none hs none) then return
    throwError "wram_call: the direct contract `{h}` does not apply to the current goal \
      (expected `ExecWithin` or `Exec` matching the goal's program)."

@[tactic_alt wramCall]
syntax (name := wramCallHints) "wram_call " term:max " [" term,* "]" " with"
  (ppSpace colGt rintroPat)+ : tactic

elab_rules : tactic
  | `(tactic| wram_call $h [$hints,*] with $pats*) => do
    if ← WramCall.withSeqPeel (WramCall.applyAuto `direct h none hints.getElems (some pats)) then
      return
    throwError "wram_call: the contract `{h}` does not apply to the current goal."

@[tactic_alt wramCall]
syntax (name := wramCallRenamed) "wram_call " term:max &" renamed"
  ppSpace colGt term:max (ppSpace colGt "[" term,* "]")?
  " with" (ppSpace colGt rintroPat)+ : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_call $h renamed $hf $[[$hints,*]]? with $pats*) => do
    let hs := (hints.map (·.getElems)).getD #[]
    if hs.isEmpty then
      let runLegacy : TacticM Bool := do
        let within ← `(tactic|
          refine Cslib.WordRAM.WP.of_spec' (Cslib.WordRAM.ExecWithin.rename_post $hf $h) ?_)
        let exact ← `(tactic|
          refine Cslib.WordRAM.WP.Exact.of_spec' (Cslib.WordRAM.Exec.rename_post $hf $h) ?_)
        for tac in [within, exact] do
          let s ← saveState
          try
            withoutRecover (evalTactic tac)
            WramCall.introWithWitness 1 pats
            return true
          catch _ => s.restore
        return false
      if ← WramCall.withSeqPeel runLegacy then return
    if ← WramCall.withSeqPeel (WramCall.applyAuto `renamed h (some hf) hs (some pats)) then
      return
    let within ← `(tactic|
      refine Cslib.WordRAM.WP.of_spec (Cslib.WordRAM.ExecWithin.rename_post $hf $h) ?_)
    let exact ← `(tactic|
      refine Cslib.WordRAM.WP.Exact.of_spec (Cslib.WordRAM.Exec.rename_post $hf $h) ?_)
    WramCall.run h [within, exact]
      (← `(tactic| rintro $pats*))
      fun
      | ``WP => some (m!"For the goal `WP w (c.rename f) x Q`, the contract must have type \
          `∃ y, ExecWithin w c (x.comap f) y T ∧ P y`, with `hf : f.Injective`.",
          [(``Exists, within)])
      | ``WP.Exact => some (m!"For the goal `WP.Exact w (c.rename f) x Q`, the contract must \
          have type `∃ y, Exec w c (x.comap f) y T ∧ P y`, with `hf : f.Injective`.",
          [(``Exists, exact)])
      | _ => none

@[tactic_alt wramCall]
syntax (name := wramCallRenamedAuto) (priority := high) "wram_call " term:max &" renamed"
  (" [" term,* "]")? " with" (ppSpace colGt rintroPat)+ : tactic

elab_rules : tactic
  | `(tactic| wram_call $h renamed $[[$hints,*]]? with $pats*) => do
    let hs := (hints.map (·.getElems)).getD #[]
    if ← WramCall.withSeqPeel (WramCall.applyAuto `renamed h none hs (some pats)) then
      return
    throwError "wram_call: could not apply renamed contract `{h}` (could not match `c.rename f` \
      or prove `f.Injective`)."

end Cslib.WordRAM
