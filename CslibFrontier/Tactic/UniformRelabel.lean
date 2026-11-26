/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Uniform
public meta import Lean.Elab.Tactic

/-!
# Relabeling and dropping uniform draws

* `relabel_uniform e [with x]`: equates `PMF` distributions whose leading uniform draws
  (`Cslib.Probability.PMF.uniformOfFintype`, collapsing nested `Prod` draws) match up to
  `e : α ≃ β` or `f : α → β`, auto-discharging standard bijectivities.
* `drop_uniform with x`: simplifies constant `PMF.bind` stages via `PMF.bind_const` and peels an
  unused leading `PMF.bind` stage `μ.bind fun y => f y = g` to `f x = g` via `bind_const_of_eq`.

## Main definitions

* `relabel_uniform`: equate uniform `PMF` draws along a bijection or map.
* `drop_uniform`: simplify constant `PMF.bind` stages and peel a leading `PMF.bind` draw.
-/

public section

namespace Cslib.Tactic.UniformRelabel

open Cslib.Probability

/-- Internal tactic bridge lemma pushing `PMF.map` through a bijection of finite nonempty types. -/
theorem uniformOfFintype_map_bijective {α β γ : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    {f : α → β} (hf : Function.Bijective f) {g : β → γ} {g' : α → γ}
    (hg : ∀ a, g' a = g (f a)) :
    (PMF.uniformOfFintype α).map g' = (PMF.uniformOfFintype β).map g :=
  PMF.uniformOfFintype_bind_bijective hf fun a => congrArg PMF.pure (hg a)

/-- Internal tactic bridge lemma proving `μ.bind f = g` from `∀ a, f a = g`. -/
theorem bind_const_of_eq {α β : Type*} (μ : PMF α) (f : α → PMF β) (g : PMF β)
    (h : ∀ a, f a = g) : μ.bind f = g := by
  rw [show f = fun _ => g from funext h, PMF.bind_const]

end Cslib.Tactic.UniformRelabel

public meta section

namespace Cslib.Tactic.UniformRelabel

open Lean Meta Elab Tactic

private def castEq (a b h : Expr) : MetaM Expr := do
  mkExpectedTypeHint h (← mkEq a b)

private def runStrict (g : MVarId) (stx : TSyntax `tactic) : TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [g]
  try withoutRecover (evalTactic stx); getGoals finally setGoals saved

private def tryWithState {α : Type} (x : TacticM (Option α)) : TacticM (Option α) := do
  let s ← saveState
  try
    let some r ← x | s.restore; return none
    return some r
  catch _ => s.restore; return none

private def closes (g : MVarId) (stx : TSyntax `tactic) : TacticM Bool := do
  return (← tryWithState do
    return if (← runStrict g stx).isEmpty then some () else none).isSome

private def mkSimpCtx (names : Array Name) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for n in names do thms ← thms.addConst n
  Simp.mkContext { zeta := false, iota := false, proj := false } #[thms] (← getSimpCongrTheorems)

/-- Normalize monad `Bind`/`Pure`/`Map`, associative `bind`/`map`, `Function.comp`, and `extra`. -/
private def normExpr (extra : Array Name := #[]) (e : Expr) : MetaM (Expr × Option Expr) := do
  let ctx ← mkSimpCtx (#[``Cslib.Probability.PMF.monad_bind_eq_bind,
    ``Cslib.Probability.PMF.monad_pure_eq_pure, ``PMF.monad_map_eq_map, ``PMF.bind_bind,
    ``PMF.bind_map, ``PMF.map_bind, ``PMF.map_comp, ``PMF.pure_bind, ``PMF.pure_map,
    ``Function.comp_def] ++ extra)
  let (r, _) ← Meta.simp e ctx
  return (r.expr, r.proof?)

private def pmfEq? (g : MVarId) : MetaM (Option (Expr × Expr)) := do
  let some (ty, l, r) := (← instantiateMVars (← g.getType)).cleanupAnnotations.eq? | return none
  return if (← whnfR ty).isAppOf ``PMF then some (l, r) else none

private def classifyMap (f : Expr) : MetaM (Expr × Expr × Expr × Bool) := do
  let fTy ← instantiateMVars (← inferType f)
  let fTyW ← whnfR fTy
  if fTyW.isAppOfArity ``Equiv 2 then
    return (← mkAppM ``DFunLike.coe #[f], fTyW.getArg! 0, fTyW.getArg! 1, true)
  if let .forallE _ α β _ := fTyW then
    if !β.hasLooseBVars then return (f, α, β, false)
  throwError "relabel_uniform: expected `α ≃ β` or `α → β`, got{indentExpr fTy}"

private inductive UniformHead where
  | bind (α cont : Expr) | map (α fn : Expr) | bare (α : Expr)

private def UniformHead.dom : UniformHead → Expr
  | .bind α _ | .map α _ | .bare α => α

private def parseUniform? (e : Expr) : Option UniformHead :=
  let e := e.cleanupAnnotations.headBeta
  let unifDom? (μ : Expr) : Option Expr :=
    let μ := μ.cleanupAnnotations.headBeta
    if μ.isAppOfArity ``Cslib.Probability.PMF.uniformOfFintype 3 then some (μ.getArg! 0) else none
  if e.isAppOfArity ``PMF.bind 4 then (unifDom? (e.getArg! 2)).map (.bind · (e.getArg! 3))
  else if e.isAppOfArity ``PMF.map 4 then (unifDom? (e.getArg! 3)).map (.map · (e.getArg! 2))
  else (unifDom? e).map .bare

private def chainOpt (a b : Expr) (h₁? h₂? : Option Expr) : MetaM (Option Expr) := do
  match h₁?, h₂? with
  | none, none => return none
  | some h, none | none, some h => return some (← castEq a b h)
  | some h₁, some h₂ => return some (← castEq a b (← mkEqTrans h₁ h₂))

private def mergeUniformPair (x L R : Expr) (isBind : Bool) (bodyLam : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let bName := match bodyLam.cleanupAnnotations with | .lam n _ _ _ => n | _ => `b
  let fnXY ← withLocalDecl bName .default R fun y =>
    mkLambdaFVars #[x, y] (mkApp bodyLam y).headBeta
  let pf ← if isBind then
    let pairTy ← mkAppM ``Prod #[L, R]
    let reflE ← mkAppOptM ``Equiv.refl #[some pairTy]
    let kPair ← withLocalDecl `p .default pairTy fun p => do
      let fst ← mkAppM ``Prod.fst #[p]
      let snd ← mkAppM ``Prod.snd #[p]
      mkLambdaFVars #[p] (mkApp2 fnXY fst snd).headBeta
    mkAppM ``Cslib.Probability.PMF.uniformOfFintype_bind_bind_equiv #[reflE, kPair]
  else
    mkAppM ``Cslib.Probability.PMF.uniformOfFintype_bind_map #[fnXY]
  let some (_, _, rhsExpr) := (← inferType pf).eq? | return none
  return some (rhsExpr, pf)

/-- Collapse consecutive `PMF.uniformOfFintype` draws on `e` so its outer domain matches
`targetTy` along nested product types. -/
private partial def collapseToType (targetTy e : Expr) : MetaM (Expr × Option Expr) := do
  let e0 := e.cleanupAnnotations.headBeta
  let some (.bind α _) := parseUniform? e0 | return (e0, none)
  if ← isDefEq α targetTy then return (e0, none)
  let tW ← whnfR targetTy
  if !tW.isAppOfArity ``Prod 2 then return (e0, none)
  let (L, R) := (tW.getArg! 0, tW.getArg! 1)
  let mut cur := e0
  let mut hCur? : Option Expr := none
  if !(← isDefEq α L) && (← whnfR L).isAppOfArity ``Prod 2 then
    if let (lMerged, some hl) ← collapseToType L cur then
      hCur? ← chainOpt e0 lMerged hCur? (some hl)
      cur := lMerged
  let some (.bind αNow contNow) := parseUniform? cur | return (cur, hCur?)
  if (← isDefEq αNow targetTy) || !(← isDefEq αNow L) then return (cur, hCur?)
  let xName := match contNow.cleanupAnnotations with | .lam n _ _ _ => n | _ => `a
  let (cont', hContFun?) ← withLocalDecl xName .default αNow fun x => do
    let (body', hBody?) ← collapseToType R (mkApp contNow x).headBeta
    let contLam ← mkLambdaFVars #[x] body'
    let some hBody := hBody? | return (contLam, none)
    return (contLam, some (← mkFunExt (← mkLambdaFVars #[x] hBody)))
  if let some hFun := hContFun? then
    let cur0 := cur.cleanupAnnotations.headBeta
    let mid := mkApp cur0.appFn! cont'
    hCur? ← chainOpt e0 mid hCur? (some (← mkCongrArg cur0.appFn! hFun))
    cur := mid
  let some (.bind αFinal contFinal) := parseUniform? cur | return (cur, hCur?)
  let mergeRes? ← withLocalDecl xName .default αFinal fun x => do
    let some (isBind, β, fn) := (match parseUniform? (mkApp contFinal x).headBeta with
      | some (.map β fn) => some (false, β, fn)
      | some (.bind β fn) => some (true, β, fn)
      | _ => none) | return none
    if ← isDefEq β R then mergeUniformPair x αFinal R isBind fn else return none
  if let some (merged, hMerge) := mergeRes? then
    return (merged, ← chainOpt e0 merged hCur? (some hMerge))
  return (cur, hCur?)

private def rewriteEqGoal (goal : MVarId) (lhs rhs lhs' rhs' : Expr)
    (hl? hr? : Option Expr) : MetaM MVarId := do
  if hl?.isNone && hr?.isNone then return goal
  let newGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs' rhs') (← goal.getTag)
  let mut pf := newGoal
  if let some hr := hr? then pf ← mkEqTrans pf (← mkEqSymm hr)
  if let some hl := hl? then pf ← mkEqTrans hl pf
  goal.assign (← castEq lhs rhs pf)
  return newGoal.mvarId!

private def trySolveInjective (g : MVarId) : TacticM Bool := do
  closes g (← `(tactic|
  (first
    | exact Equiv.injective _ | exact add_left_injective _ | exact add_right_injective _
    | exact sub_left_injective | exact sub_right_injective
    | (intro x y h; try dsimp only at h; try simp only [Prod.mk.injEq] at h
       try (rcases x with ⟨x₁, x₂⟩; rcases y with ⟨y₁, y₂⟩
            try dsimp only at h; try simp only [Prod.mk.injEq] at h)
       first
         | (ext; simp_all; done)
         | (try rcases h with ⟨h₁, h₂⟩; try subst_vars; try simp only [Prod.mk.injEq]
            try apply And.intro
            all_goals
              first
              | rfl | (apply add_left_cancel; assumption)
              | (apply add_right_cancel; assumption) | (simp_all; done)))
    | fail)))

private def tryRefineSplit (n : Nat) (g : MVarId) (stx : TSyntax `tactic) :
    TacticM (Option (List MVarId)) := tryWithState do
  let gs ← runStrict g stx
  return if gs.length == n then some gs else none

private def dischargeBijective (equivHint : Option Expr) (α β : Expr) (g : MVarId) :
    TacticM (List MVarId) := do
  if let some e := equivHint then g.assign (← mkAppM ``Equiv.bijective #[e]); return []
  if ← closes g (← `(tactic| (first | assumption | (apply_assumption; done)))) then return []
  if ← isDefEq α β then
    if ← closes g (← `(tactic|
        (refine Function.Involutive.bijective fun x => ?_; dsimp only
         try simp only [add_neg_cancel_right, neg_add_cancel_left, add_sub_cancel_right,
           sub_sub_cancel, Bool.not_not, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
         all_goals
           first
           | rfl
           | (ext <;> simp only [Bool.xor_assoc, Bool.xor_self,
               Bool.xor_false, Bool.not_not])))) then
      return []
    if let some [gInj] ←
        tryRefineSplit 1 g (← `(tactic| refine Finite.injective_iff_bijective.mp ?_)) then
      return if ← trySolveInjective gInj then [] else [gInj]
    return [g]
  let some [gInj, gCard] ← tryRefineSplit 2 g
      (← `(tactic| refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)) | return [g]
  let injRem := if ← trySolveInjective gInj then [] else [gInj]
  let cardOk ← closes gCard (← `(tactic|
    (try simp only [Fintype.card_prod, Fintype.card_pi, Finset.prod_mul_distrib, mul_pow, pow_add]
     all_goals (first | rfl | ac_rfl))))
  return injRem ++ (if cardOk then [] else [gCard])

private def finishContEq (var? : Option Name) (g : MVarId) : TacticM (List MVarId) := do
  let (_, g') ← match var? with | some n => g.intro n | none => g.intro1
  if ← closes g' (← `(tactic|
      ((try dsimp only)
       first | rfl | (simp only [add_zero, zero_add, sub_zero, add_sub_cancel_right]; rfl)))) then
    return []
  runStrict g' (← `(tactic| try dsimp only))

private def applyBijectiveRule (gNow : MVarId) (lUh rUh : UniformHead)
    (equivHint : Option Expr) (f srcTy dstTy : Expr) (var? : Option Name) :
    TacticM (Option (List MVarId)) := do
  let runWith (thm : Name) (g : MVarId) : TacticM (Option (List MVarId)) := do
    let [gBij, gEq] ← runStrict g
        (← `(tactic| refine $(mkIdent thm) (f := $(← Term.exprToSyntax f)) ?_ ?_))
      | return none
    return some ((← dischargeBijective equivHint srcTy dstTy gBij) ++ (← finishContEq var? gEq))
  match lUh, rUh with
  | .bind .., .bind .. | .map .., .bind .. | .bind .., .map .. =>
    runWith ``Cslib.Probability.PMF.uniformOfFintype_bind_bijective gNow
  | .map .., .map .. => runWith ``Cslib.Tactic.UniformRelabel.uniformOfFintype_map_bijective gNow
  | .map .., .bare rTy =>
    let some (_, lE, rE) := (← instantiateMVars (← gNow.getType)).eq? | return none
    let rWithId ← mkAppM ``PMF.map #[← mkAppOptM ``id #[some rTy], rE]
    let hSymm ← mkEqSymm (← mkAppM ``PMF.map_id #[rE])
    let gMap ← rewriteEqGoal gNow lE rE lE rWithId none (some hSymm)
    runWith ``Cslib.Tactic.UniformRelabel.uniformOfFintype_map_bijective gMap
  | _, _ => return none

private def tryRelabelEq (goal : MVarId) (eTerm : Expr) (var? : Option Name) :
    TacticM (Option (List MVarId)) := goal.withContext do
  let some (lhsRaw, rhsRaw) ← pmfEq? goal | return none
  let (f, srcTy, dstTy, isEquiv) ← classifyMap eTerm
  let equivHint := if isEquiv then some eTerm else none
  let (lhsN, hln?) ← normExpr #[] lhsRaw
  let (rhsN, hrn?) ← normExpr #[] rhsRaw
  let tryOrientation (flip : Bool) : TacticM (Option (List MVarId)) := tryWithState do
    let (lBase, rBase, hL0?, hR0?) :=
      if flip then (rhsN, lhsN, hrn?, hln?) else (lhsN, rhsN, hln?, hrn?)
    let mut gCur := goal
    if flip then
      let [gSymm] ← runStrict gCur (← `(tactic| apply Eq.symm)) | return none
      gCur := gSymm
    let (lCol, hlc?) ← collapseToType srcTy lBase
    let (rCol, hrc?) ← collapseToType dstTy rBase
    let (oL, oR) := if flip then (rhsRaw, lhsRaw) else (lhsRaw, rhsRaw)
    let gNow ← rewriteEqGoal gCur oL oR lCol rCol
      (← chainOpt oL lCol hL0? hlc?) (← chainOpt oR rCol hR0? hrc?)
    let some lUh := parseUniform? lCol | return none
    let some rUh := parseUniform? rCol | return none
    if !(← isDefEq lUh.dom srcTy) || !(← isDefEq rUh.dom dstTy) then return none
    applyBijectiveRule gNow lUh rUh equivHint f srcTy dstTy var?
  let sInit ← saveState
  if let some res ← tryOrientation false then
    if res.isEmpty then return some []
    if ← isDefEq srcTy dstTy then
      let sFwd ← saveState; sInit.restore
      if let some resFlip ← tryOrientation true then if resFlip.isEmpty then return some []
      sFwd.restore
    return some res
  sInit.restore
  tryOrientation true

/-- `relabel_uniform e [with x]` relabels `PMF.uniformOfFintype` draws along `e : α ≃ β` or
`f : α → β`. On a `PMF` equality it normalizes `Bind`/`Pure`/`Map` notation, collapses
consecutive uniform draws along nested products when needed, applies
`uniformOfFintype_bind_bijective` / `uniformOfFintype_map_bijective`, and auto-discharges standard
bijectivities. -/
syntax (name := relabelUniform) "relabel_uniform " term (" with " ident)? : tactic

@[inherit_doc relabelUniform]
elab_rules : tactic
  | `(tactic| relabel_uniform $eStx $[with $v?]?) => withMainContext do
    let eRaw ← elabTerm eStx none (mayPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let eTerm ← instantiateMVars eRaw
    let some remaining ← tryRelabelEq (← getMainGoal) eTerm (v?.map (·.getId))
      | throwError "relabel_uniform: no matching uniform draw equality for {eStx}"
    replaceMainGoal remaining

/-- `drop_uniform with x` simplifies constant `PMF.bind` stages via `PMF.bind_const` and peels a
leading `PMF.bind` draw `μ.bind fun y => f y = g` to `f x = g` via `bind_const_of_eq`. -/
syntax (name := dropUniform) "drop_uniform" " with " ident : tactic

@[inherit_doc dropUniform]
elab_rules : tactic
  | `(tactic| drop_uniform with $varId) => withMainContext do
    let goal ← getMainGoal
    let some (lhsRaw, rhsRaw) ← pmfEq? goal
      | throwError "drop_uniform: expected an equation of distributions `PMF _`"
    let (lhsN, hln?) ← normExpr #[``PMF.bind_const] lhsRaw
    let (rhsN, hrn?) ← normExpr #[``PMF.bind_const] rhsRaw
    let gNow ← rewriteEqGoal goal lhsRaw rhsRaw lhsN rhsN hln? hrn?
    let some (l, r) ← pmfEq? gNow | throwError "drop_uniform: internal error"
    let peelStx ←
      if l.cleanupAnnotations.headBeta.isAppOfArity ``PMF.bind 4 then
        `(tactic| refine Cslib.Tactic.UniformRelabel.bind_const_of_eq _ _ _ ?_)
      else if r.cleanupAnnotations.headBeta.isAppOfArity ``PMF.bind 4 then
        `(tactic| refine (Cslib.Tactic.UniformRelabel.bind_const_of_eq _ _ _ ?_).symm)
      else throwError "drop_uniform: neither side is a `PMF.bind` chain"
    let [gSub] ← runStrict gNow peelStx | throwError "drop_uniform: failed to peel leading bind"
    replaceMainGoal [(← gSub.intro varId.getId).2]

end Cslib.Tactic.UniformRelabel
