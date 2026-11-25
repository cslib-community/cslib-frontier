/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.RegisterFrame
public import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Canonical continuations of renamed calls

`WP.of_spec_rename` and `WP.Exact.of_spec_rename` pass the small returned state to a continuation
whose caller state is explicitly `Data.extend`. The `wram_call … canonical … with …` form handles
both `WP` (bounded-time `ExecWithin`) and `WP.Exact` (exact-count `Exec`) goals, accepts direct
`ExecWithin`/`Exec` lemmas (`wram_call h canonical`), automatically peels leading `.seq`, and
infers `f.Injective` when omitted (`wram_call h canonical with …`). The word `canonical` is not
reserved: importers may still use it as an identifier.

Outside-bank reads use the original caller; inside-bank reads need the callee's actual output
or preservation facts. Memory is the callee's returned memory, with no implied memory frame.

`Data.reduceExtendRegs` normalizes one read at a time for both symbolic banks (checking the local
context for `Function.Injective f`, `j ∉ Set.range f`, `∀ k, f k ≠ j`, `Fin.castAdd`, `Fin.castLE`,
`Fin.natAdd`, and linear `Fin.mk` definitions in O(1)) and closed finite banks. It never unfolds
the noncomputable `Function.extend` or expands an entire register function.

## Main results

* `WP.of_spec_rename`, `WP.of_spec_rename'`: canonical `WP` continuation of an existential renamed
  routine contract (and witness-retaining variant).
* `WP.of_execWithin_rename`, `WP.of_execWithin_rename_eq`: canonical `WP` continuations of direct
  `ExecWithin` contracts.
* `WP.Exact.of_spec_rename`, `WP.Exact.of_spec_rename'`, `WP.Exact.of_exec_rename`,
  `WP.Exact.of_exec_rename_eq`: exact-count counterparts on `WP.Exact`.
-/

public section

namespace Cslib.WordRAM

attribute [wram_simps] Data.comap_regs Data.comap_mem
  Data.extend_mem Matrix.cons_val_zero Matrix.cons_val_one Matrix.cons_val

/-- Continue a renamed fixed-time routine at its canonical caller state, with exact allowance. -/
theorem WP.of_spec_rename {B : Basis} {r s w T : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s}
    {P : Data r → Prop} {Q : Data s → ℕ → Prop}
    (h : ∃ y, ExecWithin w c (x.comap f) y T ∧ P y)
    (hQ : ∀ y, P y → Q (y.extend f x) T) : WP w (c.rename f) x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.of_execWithin (hy.rename hf) (hQ y hP)

/-- Witness-preserving variant of `WP.of_spec_rename`, retaining `ExecWithin w c (x.comap f) y T`
so `regs_frame` can follow `hy.regs_eq` across the small callee state `y`. -/
theorem WP.of_spec_rename' {B : Basis} {r s w T : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s}
    {P : Data r → Prop} {Q : Data s → ℕ → Prop}
    (h : ∃ y, ExecWithin w c (x.comap f) y T ∧ P y)
    (hQ : ∀ y, ExecWithin w c (x.comap f) y T → P y → Q (y.extend f x) T) :
    WP w (c.rename f) x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.of_execWithin (hy.rename hf) (hQ y hy hP)

/-- Continue a renamed direct `ExecWithin` routine at its canonical caller state `y.extend f x`. -/
theorem WP.of_execWithin_rename {B : Basis} {r s w T : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s} {y : Data r}
    {Q : Data s → ℕ → Prop} (h : ExecWithin w c (x.comap f) y T)
    (hQ : ExecWithin w c (x.comap f) y T → Q (y.extend f x) T) :
    WP w (c.rename f) x Q :=
  WP.of_execWithin (h.rename hf) (hQ h)

/-- Continue a renamed direct `ExecWithin` routine with `y' = y` binding its small state. -/
theorem WP.of_execWithin_rename_eq {B : Basis} {r s w T : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s} {y : Data r}
    {Q : Data s → ℕ → Prop} (h : ExecWithin w c (x.comap f) y T)
    (hQ : ∀ y', ExecWithin w c (x.comap f) y' T → y' = y → Q (y'.extend f x) T) :
    WP w (c.rename f) x Q :=
  WP.of_execWithin (h.rename hf) (hQ y h rfl)

/-- Continue a renamed fixed-time routine at its canonical caller state with exact instruction
count. -/
theorem WP.Exact.of_spec_rename {B : Basis} {r s w T : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s}
    {P : Data r → Prop} {Q : Data s → ℕ → Prop}
    (h : ∃ y, Exec w c (x.comap f) y T ∧ P y)
    (hQ : ∀ y, P y → Q (y.extend f x) T) : WP.Exact w (c.rename f) x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.Exact.of_exec (hy.rename hf) (hQ y hP)

/-- Witness-preserving variant of `WP.Exact.of_spec_rename`, retaining `Exec w c (x.comap f) y T`
so `regs_frame` can follow `hy.regs_eq` across the small callee state `y`. -/
theorem WP.Exact.of_spec_rename' {B : Basis} {r s w T : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s}
    {P : Data r → Prop} {Q : Data s → ℕ → Prop}
    (h : ∃ y, Exec w c (x.comap f) y T ∧ P y)
    (hQ : ∀ y, Exec w c (x.comap f) y T → P y → Q (y.extend f x) T) :
    WP.Exact w (c.rename f) x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.Exact.of_exec (hy.rename hf) (hQ y hy hP)

/-- Continue a renamed direct `Exec` routine at its canonical caller state `y.extend f x`. -/
theorem WP.Exact.of_exec_rename {B : Basis} {r s w T : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s} {y : Data r}
    {Q : Data s → ℕ → Prop} (h : Exec w c (x.comap f) y T)
    (hQ : Exec w c (x.comap f) y T → Q (y.extend f x) T) :
    WP.Exact w (c.rename f) x Q :=
  WP.Exact.of_exec (h.rename hf) (hQ h)

/-- Continue a renamed direct `Exec` routine with `y' = y` binding its small state. -/
theorem WP.Exact.of_exec_rename_eq {B : Basis} {r s w T : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s} {y : Data r}
    {Q : Data s → ℕ → Prop} (h : Exec w c (x.comap f) y T)
    (hQ : ∀ y', Exec w c (x.comap f) y' T → y' = y → Q (y'.extend f x) T) :
    WP.Exact w (c.rename f) x Q :=
  WP.Exact.of_exec (h.rename hf) (hQ y h rfl)

open Lean Meta in
/-- Normalize only the selected read of a `Data.extend` register bank. Checks local `Injective`
hypotheses, symbolic `Fin.castAdd` / `Fin.castLE` / `Fin.natAdd` maps, and linear `Fin.mk` bank
maps before falling back to closed finite-bank `decide`. -/
simproc ↓ [wram_simps] Data.reduceExtendRegs (Data.regs _ _) := fun e => do
  let_expr Data.regs s d j := e | return .continue
  let_expr Data.extend r _ f y x := d | return .continue
  let some (rhs, proof) ← RegsFrame.reduceExtendRegs? r s f y x j | return .continue
  return .visit { expr := rhs, proof? := proof }

namespace WramCall

open Lean Meta Elab Tactic

/-- Apply a canonical renamed contract (supporting both `WP` and `WP.Exact`, `Exists` specs, bare
`ExecWithin`/`Exec`, optional `hf`, auto-discharged trailing arguments, and `.seq` peeling). -/
private meta def applyCanonical (hTerm : Term) (hf? : Option Term) (hintTerms : Array Term)
    (pats? : Option (TSyntaxArray `rintroPat)) : TacticM Bool :=
    withMainContext do
  let g ← getMainGoal
  let tgt := (WP.Exec.headBetaAll (← instantiateMVars (← g.getType))).consumeMData
  let exact ←
    if tgt.isAppOfArity ``WP 6 then pure false
    else if tgt.isAppOfArity ``WP.Exact 6 then pure true
    else return false
  let g ← g.replaceTargetDefEq tgt
  let codeR ← whnfR (tgt.getArg! 3)
  unless codeR.isAppOfArity ``Code.rename 5 do return false
  let f := codeR.getArg! 3
  let hf : Expr ← match hf? with
    | some hfTerm =>
      let expectedTy ← mkAppM ``Function.Injective #[f]
      try Tactic.elabTermEnsuringType hfTerm (some expectedTy)
      catch _ => return false
    | none =>
      let some e ← RegsFrame.proveBankInjective? f | return false
      pure e
  let (hExpr, holeMVars) ← do
    let s ← saveState
    try
      let e ← Tactic.elabTerm hTerm none true
      pure (e, ← getMVars e)
    catch _ => s.restore; return false
  let hTy ← whnfR (← instantiateMVars (← inferType hExpr))
  let (teleArgs, _, concl) ← forallMetaTelescope hTy
  let names ← forallTelescope hTy fun xs _ => xs.mapM (·.fvarId!.getUserName)
  for (arg, nm) in teleArgs.zip names do
    arg.mvarId!.setTag nm
  let hApp := mkAppN hExpr teleArgs
  let concl ← whnfR (← instantiateMVars concl)
  let conclHead := concl.getAppFn.constName?
  let tryRule (ruleName : Name) (witAfter : ℕ) : TacticM (Option (MVarId × ℕ)) := do
    let s ← saveState
    try
      let c ← mkConstWithFreshMVarLevels ruleName
      let (rArgs, _, rConcl) ← forallMetaTelescope (← inferType c)
      unless ← isDefEq rConcl (← g.getType) do s.restore; return none
      let n := rArgs.size
      unless n ≥ 3 do s.restore; return none
      let argSlot := rArgs[n - 2]!
      let contSlot := rArgs[n - 1]!
      let mut assignedHf := false
      for ra in rArgs do
        let rty ← inferType ra
        if rty.isAppOf ``Function.Injective then
          if ← isDefEq ra hf then
            assignedHf := true; break
      unless assignedHf do s.restore; return none
      unless ← isDefEq (← inferType hApp) (← inferType argSlot) do s.restore; return none
      unless ← isDefEq argSlot hApp do s.restore; return none
      g.assign (← instantiateMVars (mkAppN c rArgs))
      return some (contSlot.mvarId!, witAfter)
    catch _ => s.restore; return none
  let hasPats := pats?.isSome
  let applied? : Option (MVarId × ℕ) ← match exact, conclHead with
    | false, some ``Exists => tryRule ``WP.of_spec_rename' 1
    | false, some ``ExecWithin =>
      if hasPats then tryRule ``WP.of_execWithin_rename_eq 1
      else tryRule ``WP.of_execWithin_rename 0
    | true, some ``Exists => tryRule ``WP.Exact.of_spec_rename' 1
    | true, some ``Exec =>
      if hasPats then tryRule ``WP.Exact.of_exec_rename_eq 1
      else tryRule ``WP.Exact.of_exec_rename 0
    | _, _ => pure none
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
  | some pats => introWithWitness witAfter pats
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

end WramCall

/-- Apply a renamed routine contract with its small returned state and canonical caller view
`small.extend bank caller`. Supports both `WP` and `WP.Exact`. -/
tactic_extension wramCall

@[tactic_alt wramCall]
syntax (name := wramCallCanonical) "wram_call " term:max &" canonical"
  ppSpace colGt term:max (ppSpace colGt "[" term,* "]")?
  " with" (ppSpace colGt rintroPat)+ : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_call $h canonical $hf $[[$hints,*]]? with $pats*) => do
    let hs := (hints.map (·.getElems)).getD #[]
    if hs.isEmpty then
      let runLegacy : TacticM Bool := do
        let within ← `(tactic| refine Cslib.WordRAM.WP.of_spec_rename' $hf $h ?_)
        let exact ← `(tactic| refine Cslib.WordRAM.WP.Exact.of_spec_rename' $hf $h ?_)
        for tac in [within, exact] do
          let s ← saveState
          try
            withoutRecover (evalTactic tac)
            WramCall.introWithWitness 1 pats
            return true
          catch _ => s.restore
        return false
      if ← WramCall.withSeqPeel runLegacy then return
    if ← WramCall.withSeqPeel (WramCall.applyCanonical h (some hf) hs (some pats)) then return
    let within ← `(tactic| refine Cslib.WordRAM.WP.of_spec_rename $hf $h ?_)
    let exact ← `(tactic| refine Cslib.WordRAM.WP.Exact.of_spec_rename $hf $h ?_)
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
syntax (name := wramCallCanonicalAuto) (priority := high) "wram_call " term:max &" canonical"
  (" [" term,* "]")? " with" (ppSpace colGt rintroPat)+ : tactic

elab_rules : tactic
  | `(tactic| wram_call $h canonical $[[$hints,*]]? with $pats*) => do
    let hs := (hints.map (·.getElems)).getD #[]
    if ← WramCall.withSeqPeel (WramCall.applyCanonical h none hs (some pats)) then return
    throwError "wram_call: could not apply canonical renamed contract `{h}`."

@[tactic_alt wramCall]
syntax (name := wramCallCanonicalDirect) (priority := high) "wram_call " term:max &" canonical"
  (ppSpace colGt "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wram_call $h canonical $[[$hints,*]]?) => do
    let hs := (hints.map (·.getElems)).getD #[]
    if ← WramCall.withSeqPeel (WramCall.applyCanonical h none hs none) then return
    throwError "wram_call: could not apply direct canonical renamed contract `{h}`."

@[tactic_alt wramCall]
syntax (name := wramCallCanonicalDirectHf) "wram_call " term:max &" canonical"
  ppSpace colGt term:max (ppSpace colGt "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wram_call $h canonical $hf $[[$hints,*]]?) => do
    let hs := (hints.map (·.getElems)).getD #[]
    if ← WramCall.withSeqPeel (WramCall.applyCanonical h (some hf) hs none) then return
    throwError "wram_call: could not apply direct canonical renamed contract `{h}`."

end Cslib.WordRAM
