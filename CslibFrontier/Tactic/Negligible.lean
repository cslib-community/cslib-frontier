/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Negligible.Dyadic
public import Mathlib.Basic.NNReal.Basic
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.Simp
public meta import Mathlib.Tactic.FunProp
public meta import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.Positivity

/-!
# Closing cryptographic negligibility bounds

`negligible` proves `Cslib.Crypto.Negligible f` by combining the `fun_prop` closure rules for
`Negligible`, `PolynomiallyBounded`, `PolynomiallyBoundedNNReal`, and
`PolynomiallyLowerBounded` with comparison against explicit pointwise or eventual upper bounds in
`ℝ≥0` or `ℝ`.

* `negligible` normalizes local `let` bindings, unary polynomial-time certificates
  (`ComputableInPolyTime f encUnary encUnary`), `Bool`-indexed `Negligible` hypotheses, pointwise
  `Pi` operations, and unit fractions `1 / x`, then runs `fun_prop` with arithmetic dischargers
  (`norm_num`, `positivity`, `omega`).
* `negligible [f, g]` (combinable with `using hle` or `eventually hle`) unfolds named wrapper
  definitions in the residual `Negligible` goal before normalization.
* `negligible using hle` reduces `Negligible f` along a pointwise bound `hle` proving either
  `∀ n, f n ≤ B n` in `ℝ≥0` or `∀ n, (f n : ℝ) ≤ B n` in `ℝ` (including `.toReal` bounds on
  `Game.succProbability`), pushing `Real.toNNReal` structurally through sums, products, quotients,
  powers, reciprocals, square roots, finite sums, and casts without manual `NNReal` mirror terms.
* `negligible eventually hle` performs the same reduction along an eventual bound
  `∀ᶠ n in Filter.atTop, …` in `ℝ≥0` or `ℝ`.

## Main definitions

* `negligible`: close `Cslib.Crypto.Negligible` goals directly or from a `using` / `eventually`
  upper bound.
-/

public section

namespace Cslib.Tactic.Negligible

open Lean Meta Elab Tactic Cslib.Crypto
open scoped NNReal

/-- Bound `Real.toNNReal x` by `u` when `(u : ℝ) = x`. -/
theorem toNNReal_le_of_coe_eq {u : ℝ≥0} {x : ℝ} (h : (u : ℝ) = x) : Real.toNNReal x ≤ u := by
  rw [← h, Real.toNNReal_coe]

/-- Monotonicity of `Real.toNNReal` across addition without nonnegativity hypotheses. -/
theorem toNNReal_add_le_of_le {a b : ℝ} {u₁ u₂ : ℝ≥0}
    (h₁ : Real.toNNReal a ≤ u₁) (h₂ : Real.toNNReal b ≤ u₂) :
    Real.toNNReal (a + b) ≤ u₁ + u₂ :=
  Real.toNNReal_add_le.trans (add_le_add h₁ h₂)

/-- Monotonicity of `Real.toNNReal` across `Real.sqrt` without nonnegativity hypotheses. -/
theorem toNNReal_sqrt_le_of_le {a : ℝ} {u : ℝ≥0} (h : Real.toNNReal a ≤ u) :
    Real.toNNReal (Real.sqrt a) ≤ NNReal.sqrt u := by
  rw [Real.sqrt, Real.toNNReal_coe, NNReal.sqrt_le_sqrt]
  exact h

/-- Pull `Nat.cast` out across `+ 1` in `ℝ≥0`. -/
theorem natCast_add_one_eq (m : ℕ) : (m : ℝ≥0) + 1 = ((m + 1 : ℕ) : ℝ≥0) :=
  (Nat.cast_add_one m).symm

/-- Pull `Nat.cast` out across `1 +` in `ℝ≥0`. -/
theorem one_add_natCast_eq (m : ℕ) : 1 + (m : ℝ≥0) = ((1 + m : ℕ) : ℝ≥0) := by
  simpa only [Nat.cast_one] using (Nat.cast_add 1 m).symm

/-- Pull `Nat.cast` out across `+ ofNat(k)` in `ℝ≥0`. -/
theorem natCast_add_ofNat_eq (m k : ℕ) [k.AtLeastTwo] :
    (m : ℝ≥0) + ofNat(k) = ((m + ofNat(k) : ℕ) : ℝ≥0) :=
  (Nat.cast_add m ofNat(k)).symm

/-- Pull `Nat.cast` out across `ofNat(k) +` in `ℝ≥0`. -/
theorem ofNat_add_natCast_eq (k m : ℕ) [k.AtLeastTwo] :
    (ofNat(k) : ℝ≥0) + (m : ℝ≥0) = ((ofNat(k) + m : ℕ) : ℝ≥0) :=
  (Nat.cast_add ofNat(k) m).symm

/-- Pull `Nat.cast` out across `ofNat(k) *` in `ℝ≥0`. -/
theorem ofNat_mul_natCast_eq (k m : ℕ) [k.AtLeastTwo] :
    (ofNat(k) : ℝ≥0) * (m : ℝ≥0) = ((ofNat(k) * m : ℕ) : ℝ≥0) :=
  (Nat.cast_mul ofNat(k) m).symm

/-- Pull `Nat.cast` out across `* ofNat(k)` in `ℝ≥0`. -/
theorem natCast_mul_ofNat_eq (m k : ℕ) [k.AtLeastTwo] :
    (m : ℝ≥0) * ofNat(k) = ((m * ofNat(k) : ℕ) : ℝ≥0) :=
  (Nat.cast_mul m ofNat(k)).symm

/-- Certificate lemmas deriving `Cslib.PolynomiallyBounded` from local unary polynomial-time
hypotheses when their module is imported. -/
private meta def unaryPolyCertificateLemmas : List Name :=
  [`Turing.MultiTapeTM.ComputableInPolyTime.polynomiallyBounded]

/-- Apply a unary polynomial-time certificate lemma `lem` to local hypothesis `h`, if it unifies. -/
private meta def applyUnaryCertificate? (lem : Name) (h : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  unless env.contains lem do return none
  let c ← mkConstWithFreshMVarLevels lem
  let (args, binders, _) ← forallMetaTelescopeReducing (← inferType c)
  let some i := (List.range args.size).reverse.find? (binders[·]!.isExplicit) | return none
  let saved ← saveState
  let ok ← withReducible (isDefEq (← inferType args[i]!) (← inferType h))
  unless ok do
    saved.restore
    return none
  args[i]!.mvarId!.assign h
  let pf ← instantiateMVars (mkAppN c args)
  if pf.hasExprMVar then
    saved.restore
    return none
  return some pf

/-- Whether `ty` is `ℕ`, `ℝ≥0`, `ℝ`, or `ℕ → ℕ` / `ℕ → ℝ≥0` / `ℕ → ℝ`. -/
private meta def isScalarOrParamFunType (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  if ty.isConstOf ``Nat || ty.isConstOf ``NNReal || ty.isConstOf ``Real then
    return true
  match ty with
  | .forallE _ d b _ =>
    if !d.isConstOf ``Nat || b.hasLooseBVars then return false
    let b ← whnfR b
    return b.isConstOf ``Nat || b.isConstOf ``NNReal || b.isConstOf ``Real
  | _ => return false

/-- Whether `ty` is `ℕ → ℕ` up to reducible unfolding. -/
private meta def isNatToNatType (ty : Expr) : MetaM Bool := do
  match ← whnfR ty with
  | .forallE _ d b _ => return d.isConstOf ``Nat && !b.hasLooseBVars && (← whnfR b).isConstOf ``Nat
  | _ => return false

/-- Expand inline `Expr.letE` nodes and local `let` declarations satisfying `shouldUnfold`, then
beta-reduce. -/
private meta partial def expandSelectedLets (shouldUnfold : FVarId → Bool) (e : Expr) :
    MetaM Expr := do
  let step (e : Expr) : MetaM TransformStep := do
    match e with
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | .fvar id =>
      if shouldUnfold id then
        if let some v ← id.getValue? then
          return .visit v
      return .continue
    | _ => return .continue
  Core.betaReduce (← Meta.transform (← instantiateMVars e) (pre := step))

/-- Try proving `PolynomiallyBounded p` in `g`'s context via `fun_prop` without unfolding local
`let` bindings. -/
private meta def provePolynomiallyBoundedOnGoal? (g : MVarId) (p : Expr) : MetaM (Option Expr) :=
  g.withContext do
    let saved ← saveState
    let goalTy := mkApp (mkConst ``Cslib.PolynomiallyBounded) p
    let mvar ← mkFreshExprSyntheticOpaqueMVar goalTy
    try
      let gs ← (Tactic.run mvar.mvarId! do
        withConfig (fun cfg => { cfg with zetaDelta := false }) do
          evalTactic (← `(tactic| fun_prop))).run'
      unless gs.isEmpty do
        saved.restore
        return none
      let pf ← instantiateMVars mvar
      if pf.hasExprMVar then
        saved.restore
        return none
      return some pf
    catch _ =>
      saved.restore
      return none

/-- Try proving `0 ≤ x` in `ℝ` using `positivity` or `norm_num`. -/
private meta def proveRealNonneg? (x : Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  let zero ← mkNumeral (mkConst ``Real) 0
  let goalTy ← mkAppM ``LE.le #[zero, x]
  let mvar ← mkFreshExprSyntheticOpaqueMVar goalTy
  try
    let gs ← (Tactic.run mvar.mvarId! do
      evalTactic (← `(tactic| first | positivity | norm_num))).run'
    unless gs.isEmpty do
      saved.restore
      return none
    let pf ← instantiateMVars mvar
    if pf.hasExprMVar then
      saved.restore
      return none
    return some pf
  catch _ =>
    saved.restore
    return none

/-- Structurally lift a nonnegative `x : ℝ` to `(u : ℝ≥0, hcoe : (u : ℝ) = x)`, or `none`. -/
private meta partial def liftNonnegReal? (x : Expr) : MetaM (Option (Expr × Expr)) := do
  let x := (← instantiateMVars x).consumeMData
  if x.isAppOfArity ``NNReal.toReal 1 then
    return some (x.appArg!, ← mkEqRefl x)
  if x.isAppOfArity ``Subtype.val 2 then
    if (← inferType x.appArg!).isConstOf ``NNReal then
      return some (x.appArg!, ← mkEqRefl x)
  if x.isAppOfArity ``ENNReal.toReal 1 then
    let u ← mkAppM ``ENNReal.toNNReal #[x.appArg!]
    return some (u, ← mkEqRefl x)
  if x.isAppOfArity ``Nat.cast 3 then
    let m := x.appArg!
    let u ← mkAppOptM ``Nat.cast #[some (mkConst ``NNReal), none, some m]
    let pf ← mkAppM ``NNReal.coe_natCast #[m]
    return some (u, pf)
  if x.isAppOfArity ``OfNat.ofNat 3 then
    if let some k := (x.getArg! 1).rawNatLit? then
      let u ← mkNumeral (mkConst ``NNReal) k
      return some (u, ← mkEqRefl x)
  if x.isAppOfArity ``Zero.zero 2 then
    let u ← mkNumeral (mkConst ``NNReal) 0
    return some (u, mkConst ``NNReal.coe_zero)
  if x.isAppOfArity ``One.one 2 then
    let u ← mkNumeral (mkConst ``NNReal) 1
    return some (u, mkConst ``NNReal.coe_one)
  for (opName, coeLem) in #[(``HAdd.hAdd, ``NNReal.coe_add), (``HMul.hMul, ``NNReal.coe_mul),
      (``HDiv.hDiv, ``NNReal.coe_div)] do
    if x.isAppOfArity opName 6 && (x.getArg! 0).isConstOf ``Real &&
        (x.getArg! 1).isConstOf ``Real then
      if let some (u₁, h₁) ← liftNonnegReal? (x.getArg! 4) then
        if let some (u₂, h₂) ← liftNonnegReal? (x.getArg! 5) then
          let u ← mkAppM opName #[u₁, u₂]
          let hcoe ← mkAppM coeLem #[u₁, u₂]
          let hcong ← mkCongr (← mkCongrArg x.appFn!.appFn! h₁) h₂
          return some (u, ← mkEqTrans hcoe hcong)
  if x.isAppOfArity ``Inv.inv 3 && (x.getArg! 0).isConstOf ``Real then
    if let some (u₁, h₁) ← liftNonnegReal? x.appArg! then
      let u ← mkAppM ``Inv.inv #[u₁]
      let hinv ← mkAppM ``NNReal.coe_inv #[u₁]
      let hcong ← mkCongrArg x.appFn! h₁
      return some (u, ← mkEqTrans hinv hcong)
  if x.isAppOfArity ``HPow.hPow 6 && (x.getArg! 0).isConstOf ``Real &&
      (x.getArg! 1).isConstOf ``Nat then
    let k := x.getArg! 5
    if let some (u₁, h₁) ← liftNonnegReal? (x.getArg! 4) then
      let u ← mkAppM ``HPow.hPow #[u₁, k]
      let hpow ← mkAppM ``NNReal.coe_pow #[u₁, k]
      let hcong ← mkCongrFun (← mkCongrArg x.appFn!.appFn! h₁) k
      return some (u, ← mkEqTrans hpow hcong)
  if x.isAppOfArity ``Real.sqrt 1 then
    if let some (u₁, h₁) ← liftNonnegReal? x.appArg! then
      let u ← mkAppM ``DFunLike.coe #[mkConst ``NNReal.sqrt, u₁]
      let hsqrt ← mkAppOptM ``Real.coe_sqrt #[some u₁]
      let hcong ← mkCongrArg (mkConst ``Real.sqrt) h₁
      return some (u, ← mkEqTrans hsqrt hcong)
  if x.isAppOfArity ``Finset.sum 5 && (x.getArg! 1).isConstOf ``Real then
    let s := x.getArg! 3
    let f := x.getArg! 4
    if let .forallE idxName dom _ _ ← whnf (← inferType f) then
      let res? ← withLocalDeclD idxName dom fun i => do
        let body := (mkApp f i).headBeta
        let some (uBody, hBody) ← liftNonnegReal? body | return none
        let uLam ← mkLambdaFVars #[i] uBody
        let memTy ← mkAppM ``Membership.mem #[s, i]
        let hLam ← withLocalDeclD `hi memTy fun hi => mkLambdaFVars #[i, hi] hBody
        return some (uLam, hLam)
      if let some (uLam, hLam) := res? then
        let u ← mkAppM ``Finset.sum #[s, uLam]
        let hsum ← mkAppM ``NNReal.coe_sum #[s, uLam]
        let hcong ← mkAppM ``Finset.sum_congr #[← mkEqRefl s, hLam]
        return some (u, ← mkEqTrans hsum hcong)
  if let some hnonneg ← proveRealNonneg? x then
    let u ← mkAppM ``Real.toNNReal #[x]
    let pf ← mkAppM ``Real.coe_toNNReal #[x, hnonneg]
    return some (u, pf)
  return none

/-- Bound `Real.toNNReal x` above by `u : ℝ≥0`, returning `(u, pf : x.toNNReal ≤ u)`. -/
private meta partial def boundToNNReal (x : Expr) : MetaM (Expr × Expr) := do
  let x := (← instantiateMVars x).consumeMData
  if let some (u, hcoe) ← liftNonnegReal? x then
    let pf ← mkAppM ``toNNReal_le_of_coe_eq #[hcoe]
    return (u, pf)
  if x.isAppOfArity ``HAdd.hAdd 6 && (x.getArg! 0).isConstOf ``Real &&
      (x.getArg! 1).isConstOf ``Real then
    let (u₁, h₁) ← boundToNNReal (x.getArg! 4)
    let (u₂, h₂) ← boundToNNReal (x.getArg! 5)
    let u ← mkAppM ``HAdd.hAdd #[u₁, u₂]
    let pf ← mkAppM ``toNNReal_add_le_of_le #[h₁, h₂]
    return (u, pf)
  if x.isAppOfArity ``Real.sqrt 1 then
    let (u₁, h₁) ← boundToNNReal x.appArg!
    let u ← mkAppM ``DFunLike.coe #[mkConst ``NNReal.sqrt, u₁]
    let pf ← mkAppM ``toNNReal_sqrt_le_of_le #[h₁]
    return (u, pf)
  let u ← mkAppM ``Real.toNNReal #[x]
  let pf ← mkAppM ``le_refl #[u]
  return (u, pf)

/-- Replace a goal `Negligible (fun n => Real.toNNReal (B n))` by `Negligible (fun n => U n)` where
`Real.toNNReal (B n)` is pushed inward to `U n : ℝ≥0`. -/
private meta def pushGoalToNNReal : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let target := (← instantiateMVars (← g.getType)).consumeMData
  unless target.isAppOfArity ``Cslib.Crypto.Negligible 1 do return
  let fn ← Core.betaReduce (← etaExpand target.appArg!)
  let .lam paramName paramDom body _ := fn | return
  unless body.isAppOfArity ``Real.toNNReal 1 do return
  let realBody := body.appArg!
  let (uFn, hleFn) ← withLocalDeclD paramName paramDom fun n => do
    let realAtN ← expandSelectedLets (fun _ => false) (realBody.instantiate1 n)
    let (uAtN, pfAtN) ← boundToNNReal realAtN
    return (← mkLambdaFVars #[n] uAtN, ← mkLambdaFVars #[n] pfAtN)
  let newGoalTy := mkApp (mkConst ``Cslib.Crypto.Negligible) uFn
  let newMVar ← mkFreshExprSyntheticOpaqueMVar newGoalTy
  let proof ← mkAppM ``Cslib.Crypto.negligible_of_le #[newMVar, hleFn]
  g.assign proof
  replaceMainGoal [newMVar.mvarId!]

/-- Harvest `PolynomiallyBounded` facts from local unary `ComputableInPolyTime` hypotheses and
local `ℕ → ℕ` `let` bindings, then unfold remaining numeric `let`s not referenced by local
`Negligible` hypotheses. -/
private meta def prepareNegligibleContext : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  let lctx ← getLCtx
  -- Collect `fvarId`s mentioned inside local `Negligible` hypotheses so we keep them intact.
  let mut protectedFVars : FVarIdSet := {}
  let mut numericLetIds : FVarIdSet := {}
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let tyR ← whnfR ty
    if (tyR.find? (·.isConstOf ``Cslib.Crypto.Negligible)).isSome then
      for id in (collectFVars {} tyR).fvarIds do
        protectedFVars := protectedFVars.insert id
    if decl.isLet then
      if ← isScalarOrParamFunType ty then
        numericLetIds := numericLetIds.insert decl.fvarId

  -- Assert polynomial-bound and `Bool`-specialized `Negligible` hypotheses from local context.
  let mut newHyps : Array Hypothesis := #[]
  let mut knownPolyFns : Array Expr := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars decl.type)
    if ty.isAppOfArity ``Cslib.PolynomiallyBounded 1 then
      knownPolyFns := knownPolyFns.push ty.appArg!

  for decl in lctx do
    if decl.isImplementationDetail || decl.isLet then continue
    let ty ← instantiateMVars decl.type
    if ← isProp ty then
      let tyR ← whnfR ty
      if let .forallE _ dom body _ := tyR then
        if (← whnfR dom).isConstOf ``Bool then
          let tyFalse := body.instantiate1 (mkConst ``Bool.false)
          if (← whnfR tyFalse).consumeMData.isAppOfArity ``Cslib.Crypto.Negligible 1 then
            let tyTrue := body.instantiate1 (mkConst ``Bool.true)
            newHyps := newHyps.push {
              userName := decl.userName.appendAfter "_false"
              type := tyFalse
              value := mkApp decl.toExpr (mkConst ``Bool.false)
            }
            newHyps := newHyps.push {
              userName := decl.userName.appendAfter "_true"
              type := tyTrue
              value := mkApp decl.toExpr (mkConst ``Bool.true)
            }
      let mut candidates : Array (Expr × Expr) := #[(decl.toExpr, tyR)]
      if tyR.isAppOfArity ``And 2 then
        candidates := candidates.push
          (← mkAppM ``And.left #[decl.toExpr], ← whnfR (tyR.getArg! 0))
        candidates := candidates.push
          (← mkAppM ``And.right #[decl.toExpr], ← whnfR (tyR.getArg! 1))
      for (cand, candTy) in candidates do
        if candTy.isAppOf `Turing.MultiTapeTM.ComputableInPolyTime then
          for lem in unaryPolyCertificateLemmas do
            if let some pf ← applyUnaryCertificate? lem cand then
              let pfTy ← instantiateMVars (← inferType pf)
              if pfTy.isAppOfArity ``Cslib.PolynomiallyBounded 1 then
                unless knownPolyFns.any (· == pfTy.appArg!) do
                  newHyps := newHyps.push { userName := `hpoly_cert, type := pfTy, value := pf }
                  knownPolyFns := knownPolyFns.push pfTy.appArg!

  if !newHyps.isEmpty then
    let (_, g') ← g.assertHypotheses newHyps
    g := g'

  -- Incrementally derive `PolynomiallyBounded` for local `ℕ → ℕ` `let` bindings without
  -- transitively unfolding already-certified `let`s.
  let letFVarIds ← g.withContext do
    let mut ids : Array FVarId := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || !decl.isLet then continue
      if ← isNatToNatType (← instantiateMVars decl.type) then
        ids := ids.push decl.fvarId
    return ids
  for fvarId in letFVarIds do
    let fnExpr := mkFVar fvarId
    if knownPolyFns.any (· == fnExpr) then
      protectedFVars := protectedFVars.insert fvarId
    else
      let hyp? ← g.withContext do
        let some decl := (← getLCtx).find? fvarId | return none
        let some val := decl.value? | return none
        let expanded ← expandSelectedLets
          (fun id => numericLetIds.contains id && !protectedFVars.contains id) val
        let some hp ← provePolynomiallyBoundedOnGoal? g expanded | return none
        let hypTy := mkApp (mkConst ``Cslib.PolynomiallyBounded) fnExpr
        unless ← isDefEq hypTy (← inferType hp) do return none
        let hinted ← mkExpectedTypeHint hp hypTy
        return some ({
          userName := decl.userName.appendAfter "_poly"
          type := hypTy
          value := hinted
        } : Hypothesis)
      if let some hyp := hyp? then
        let (_, g') ← g.assertHypotheses #[hyp]
        g := g'
        knownPolyFns := knownPolyFns.push fnExpr
        protectedFVars := protectedFVars.insert fvarId

  -- Unfold inline `let`s and unprotected local numeric `let`s in the target.
  g ← g.withContext do
    let target ← instantiateMVars (← g.getType)
    let expanded ← expandSelectedLets
      (fun id => numericLetIds.contains id && !protectedFVars.contains id) target
    if expanded == target then pure g else g.replaceTargetDefEq expanded
  replaceMainGoal [g]

/-- Normalize pointwise `Pi` operations and `1 / x` in the main `Negligible` goal and any local
`Negligible` hypotheses that contain `/` or pointwise `+` / `*`. -/
private meta def normalizeNegligibleForms : TacticM Unit := withMainContext do
  -- Eta-expand the argument of `Negligible` so `Pi.add_apply` / `Pi.mul_apply` fire.
  let g ← getMainGoal
  let target := (← instantiateMVars (← g.getType)).consumeMData
  if target.isAppOfArity ``Cslib.Crypto.Negligible 1 then
    let fn ← etaExpand target.appArg!
    if fn != target.appArg! then
      let g' ← g.replaceTargetDefEq (mkApp target.appFn! fn)
      replaceMainGoal [g']
  try
    evalTactic (← `(tactic|
      simp (config := { zetaDelta := false }) only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
        one_div, div_eq_mul_inv, one_mul, mul_inv, pow_add, ← inv_pow, ← Nat.cast_pow,
        ← Nat.cast_mul, ← Nat.cast_add, natCast_add_one_eq, one_add_natCast_eq,
        natCast_add_ofNat_eq, ofNat_add_natCast_eq, ofNat_mul_natCast_eq, natCast_mul_ofNat_eq]))
  catch _ => pure ()
  if (← getUnsolvedGoals).isEmpty then return
  withMainContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      unless (ty.find? (·.isConstOf ``Cslib.Crypto.Negligible)).isSome do continue
      let needsNorm := (ty.find? fun e =>
        e.isConstOf ``HDiv.hDiv || e.isConstOf ``HAdd.hAdd || e.isConstOf ``HMul.hMul ||
        e.isConstOf ``Inv.inv).isSome
      if needsNorm then
        let ident := mkIdent decl.userName
        try
          evalTactic (← `(tactic|
            simp (config := { zetaDelta := false }) only [Pi.add_apply, Pi.mul_apply,
              Pi.pow_apply, one_div, div_eq_mul_inv, one_mul, mul_inv, ← inv_pow] at $ident:ident))
        catch _ => pure ()

/-- Traverse 6-argument binary arithmetic applications in `binOps` (visiting both operands
`args[4]!` and `args[5]!`) and `HPow.hPow` (visiting only the base `args[4]!` and leaving the
exponent `args[5]!` untouched), rebuilding modified nodes with `mkApp4`/`mkApp2`. -/
private meta def walkBinaryAndPow (binOps : Array Name)
    (recur : Expr → MetaM (Expr × Bool)) (c e : Expr) :
    MetaM (Option (Expr × Bool)) := do
  for opName in binOps do
    if c.isAppOfArity opName 6 then
      let args := c.getAppArgs
      let (l', ml) ← recur args[4]!
      let (r', mr) ← recur args[5]!
      if ml || mr then
        let pre := mkApp4 c.getAppFn args[0]! args[1]! args[2]! args[3]!
        return some (mkApp2 pre l' r', true)
      else
        return some (e, false)
  if c.isAppOfArity ``HPow.hPow 6 then
    let args := c.getAppArgs
    let (b', mb) ← recur args[4]!
    if mb then
      let pre := mkApp4 c.getAppFn args[0]! args[1]! args[2]! args[3]!
      return some (mkApp2 pre b' args[5]!, true)
    else
      return some (e, false)
  return none

/-- Replace occurrences in a `ℕ` expression `e` matching `pat` at `.instances` transparency
(without unfolding `let` bindings or `def`s) by `replacement`. -/
private meta partial def replaceNatAtInstances (pat replacement e : Expr) :
    MetaM (Expr × Bool) := do
  if !e.hasLooseBVars then
    let matched ← withConfig (fun cfg => { cfg with zetaDelta := false }) do
      withNewMCtxDepth (withReducibleAndInstances (isDefEq e pat))
    if matched then
      return (replacement, true)
  let c := e.cleanupAnnotations
  if let some res ←
      walkBinaryAndPow #[``HAdd.hAdd, ``HMul.hMul] (replaceNatAtInstances pat replacement) c e then
    return res
  if c.isApp && c.getAppNumArgs == 1 then
    if (← inferType c.appArg!).isConstOf ``Nat then
      let (a', ma) ← replaceNatAtInstances pat replacement c.appArg!
      if ma then return (mkApp c.appFn! a', true)
  return (e, false)

/-- Walk `NNReal` arithmetic combinators (`+`, `*`, `/`, `^`, `Inv.inv`, `NNReal.sqrt`,
`Finset.sum`), replacing any subterm where `onSubterm` returns `some replacement`. -/
private meta partial def walkNNRealCombinators (onSubterm : Expr → MetaM (Option Expr))
    (e : Expr) : MetaM (Expr × Bool) := do
  if let some e' ← onSubterm e then
    return (e', true)
  let c := e.cleanupAnnotations
  if let some res ← walkBinaryAndPow #[``HAdd.hAdd, ``HMul.hMul, ``HDiv.hDiv]
      (walkNNRealCombinators onSubterm) c e then
    return res
  if c.isAppOfArity ``Inv.inv 3 then
    let args := c.getAppArgs
    let (a', ma) ← walkNNRealCombinators onSubterm args[2]!
    if ma then
      return (mkApp (mkApp2 c.getAppFn args[0]! args[1]!) a', true)
    else
      return (e, false)
  if c.isAppOfArity ``DFunLike.coe 6 then
    let args := c.getAppArgs
    let (a', ma) ← walkNNRealCombinators onSubterm args[5]!
    if ma then
      return (mkApp c.appFn! a', true)
    else
      return (e, false)
  if c.isAppOfArity ``Finset.sum 5 then
    let args := c.getAppArgs
    let f := args[4]!
    if let .forallE idxName dom _ _ ← whnf (← inferType f) then
      let (f', mf) ← withLocalDeclD idxName dom fun i => do
        let (body', mb) ← walkNNRealCombinators onSubterm (mkApp f i).headBeta
        if mb then return (← mkLambdaFVars #[i] body', true) else return (f, false)
      if mf then
        return (mkApp (mkApp4 c.getAppFn args[0]! args[1]! args[2]! args[3]!) f', true)
  return (e, false)

/-- Abstract one local `predName fn` hypothesis whose pointwise value `fn n` occurs in `gGoal`
(rewritten by `replaceBody`) into fresh `(fn_var : Nat -> cod) (hfn : predName fn_var)`. -/
private meta def abstractHypothesisAt (gGoal : MVarId) (fvarId : FVarId) (predName : Name)
    (codTy : Expr) (noZetaCheck : Bool)
    (replaceBody : Expr → Expr → Expr → MetaM (Expr × Bool)) : MetaM MVarId :=
  gGoal.withContext do
    let some decl := (← getLCtx).find? fvarId | return gGoal
    let ty ← whnfR (← instantiateMVars decl.type)
    unless ty.consumeMData.isAppOfArity predName 1 do return gGoal
    let gFn := ty.consumeMData.appArg!
    let target := (← instantiateMVars (← gGoal.getType)).consumeMData
    unless target.isAppOfArity ``Cslib.Crypto.Negligible 1 do return gGoal
    let targetFn ← Core.betaReduce (← etaExpand target.appArg!)
    let .lam paramName paramDom curBody _ := targetFn | return gGoal
    let fnTy ← mkArrow (mkConst ``Nat) codTy
    let absRes? ← withLocalDeclD (decl.userName.appendAfter "_fn") fnTy fun fnFVar => do
      let (newLam, matched) ← withLocalDeclD paramName paramDom fun n => do
        let pat := (mkApp gFn n).headBeta
        let (body', m) ← replaceBody pat (mkApp fnFVar n) (curBody.instantiate1 n)
        return (← mkLambdaFVars #[n] body', m)
      if !matched then return none
      let newTarget := mkApp (mkConst ``Cslib.Crypto.Negligible) newLam
      let absPred ← mkLambdaFVars #[fnFVar] newTarget
      let predFnTy := mkApp (mkConst predName) fnFVar
      let forallProp ← withLocalDeclD decl.userName predFnTy fun hfn => do
        mkForallFVars #[fnFVar, hfn] newTarget
      return some (absPred, forallProp)
    let some (absPred, forallProp) := absRes? | return gGoal
    let instTarget := (mkApp absPred gFn).headBeta
    let checkDefEq := withNewMCtxDepth (withReducibleAndInstances (isDefEq target instTarget))
    let ok ← if noZetaCheck then
        withConfig (fun cfg => { cfg with zetaDelta := false }) checkDefEq
      else
        checkDefEq
    unless ok do return gGoal
    let gGoal' ← gGoal.replaceTargetDefEq instTarget
    let predGFnTy := mkApp (mkConst predName) gFn
    let hProof ← mkExpectedTypeHint decl.toExpr predGFnTy
    let mvar ← mkFreshExprSyntheticOpaqueMVar forallProp
    gGoal'.assign (mkApp2 mvar gFn hProof)
    let (_, gNext) ← mvar.mvarId!.introNP 2
    try gNext.clear fvarId catch _ => pure gNext

/-- Collect non-trivial local hypothesis IDs with head `predName` (skipping plain `cdecl` fvar
arguments unless `includeLetFVars` holds and the argument is a local `let`). -/
private meta def collectAbstractableHypIds (gGoal : MVarId) (predName : Name)
    (includeLetFVars : Bool) : MetaM (Array FVarId) :=
  gGoal.withContext do
    let mut ids : Array FVarId := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || decl.isLet then continue
      let ty ← whnfR (← instantiateMVars decl.type)
      unless ty.consumeMData.isAppOfArity predName 1 do continue
      let arg := ty.consumeMData.appArg!.eta
      if arg.isFVar then
        if includeLetFVars then
          if let some argDecl := (← getLCtx).find? arg.fvarId! then
            if !argDecl.isLet then continue
        else
          continue
      ids := ids.push decl.fvarId
    return ids

/-- Abstract local `Negligible g` and composite/`let`-backed `PolynomiallyBounded p` hypotheses
whose pointwise values appear in the goal (up to `.instances` transparency) into fresh local `cdecl`
variables so `fun_prop` never unfolds distinct `def` games, composite projections, or chained local
`let` definitions. -/
private meta def abstractNegligibleHypotheses : TacticM Unit := withMainContext do
  let mut gGoal ← getMainGoal
  -- Abstract complete `Negligible` leaves first so the polynomial pass cannot rewrite inside them.
  let candIds ← collectAbstractableHypIds gGoal ``Cslib.Crypto.Negligible false
  let replaceNegl (pat replacement e : Expr) : MetaM (Expr × Bool) :=
    walkNNRealCombinators (fun sub => do
      if !sub.hasLooseBVars then
        if ← withNewMCtxDepth (withReducibleAndInstances (isDefEq sub pat)) then
          return some replacement
      return none) e
  for fvarId in candIds do
    gGoal ← abstractHypothesisAt gGoal fvarId ``Cslib.Crypto.Negligible (mkConst ``NNReal) false
      replaceNegl
  let polyCandIds ← collectAbstractableHypIds gGoal ``Cslib.PolynomiallyBounded true
  let replacePoly (pat replacement e : Expr) : MetaM (Expr × Bool) :=
    walkNNRealCombinators (fun sub => do
      let c := sub.cleanupAnnotations
      if c.isAppOfArity ``Nat.cast 3 then
        let (m', mm) ← replaceNatAtInstances pat replacement (c.getArg! 2)
        return if mm then some (mkApp c.appFn! m') else none
      return none) e
  for fvarId in polyCandIds do
    gGoal ← abstractHypothesisAt gGoal fvarId ``Cslib.PolynomiallyBounded (mkConst ``Nat) true
      replacePoly
  replaceMainGoal [gGoal]

/-- Apply a pointwise or eventual upper bound `hle` in `ℝ≥0` or `ℝ`. -/
private meta def applyBound (eventually : Bool) (hle : TSyntax `term) : TacticM Unit := do
  let saved ← saveState
  let nnrealTac ← if eventually then
      `(tactic| refine Cslib.Crypto.negligible_of_eventually_le ?_ $hle)
    else
      `(tactic| refine Cslib.Crypto.negligible_of_le ?_ $hle)
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic nnrealTac
    return
  catch _ =>
    saved.restore
  let realTac ← if eventually then
      `(tactic| refine Cslib.Crypto.negligible_of_eventually_coe_le ?_ $hle)
    else
      `(tactic| refine Cslib.Crypto.negligible_of_coe_le ?_ $hle)
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic realTac
    pushGoalToNNReal
  catch ex =>
    saved.restore
    let g ← getMainGoal
    let target ← instantiateMVars (← g.getType)
    let mode :=
      if eventually then "eventually (`∀ᶠ n in Filter.atTop, …`)" else "pointwise (`∀ n, …`)"
    let detail := match ex with
      | .error _ msg => m!"\n{msg}"
      | .internal _ _ => m!""
    throwError "negligible: could not apply {mode} upper bound `{hle}` to goal:\
      {indentExpr target}\n\
      Expected a bound in `ℝ≥0` (`f n ≤ B n`) or `ℝ` (`(f n : ℝ) ≤ B n`).{detail}"

/-- Optional bracketed identifier list `[f₁, f₂, …]` for `negligible`. -/
syntax neglUnfolds := " [" ident,+ "]"

/-- Pointwise bound clause `using hle` for `negligible`. -/
syntax negligibleUsingClause := " using " term

/-- Eventual bound clause `eventually hle` for `negligible`. -/
syntax negligibleEventuallyClause := ppSpace &"eventually" ppSpace term

/-- `negligible` proves `Cslib.Crypto.Negligible f` using `fun_prop` closure rules for polynomial
losses, dyadic reciprocals `((2 : ℝ≥0) ^ n)⁻¹` and `1 / 2 ^ n`, birthday bounds, square roots,
geometric decay, parameter shifts/scalings, and finite range sums.

* `negligible [f, g]` unfolds named wrapper definitions in the `Negligible` goal before
  normalization (combinable with `using hle` or `eventually hle`).
* `negligible using hle` first reduces the goal along `hle`, where `hle` proves either
  `∀ n, f n ≤ B n` in `ℝ≥0` or `∀ n, (f n : ℝ) ≤ B n` in `ℝ`.
* `negligible eventually hle` first reduces the goal along `hle`, where `hle` proves either
  `∀ᶠ n in Filter.atTop, f n ≤ B n` in `ℝ≥0` or `∀ᶠ n in Filter.atTop, (f n : ℝ) ≤ B n` in `ℝ`. -/
syntax (name := negligibleTactic) "negligible" (neglUnfolds)?
  (negligibleUsingClause <|> negligibleEventuallyClause)? : tactic

/-- Elaborate `negligible`, `negligible [defs]`, `negligible using hle`, and
`negligible eventually hle`. -/
@[tactic negligibleTactic]
meta def evalNegligible : Tactic := fun stx => focus <| withMainContext do
  let g ← getMainGoal
  let rawTarget ← instantiateMVars (← g.getType)
  let whnfTarget ← whnfR rawTarget
  unless whnfTarget.consumeMData.isAppOfArity ``Cslib.Crypto.Negligible 1 do
    throwError "negligible: expected a goal `Cslib.Crypto.Negligible f`, got:{indentExpr rawTarget}"
  if whnfTarget != rawTarget then
    replaceMainGoal [← g.replaceTargetDefEq whnfTarget]
  let (unfolds?, bound?) ← match stx with
    | `(tactic| negligible $[$u:neglUnfolds]? $[using $hle]?) =>
      pure (u, hle.map (false, ·))
    | `(tactic| negligible $[$u:neglUnfolds]? eventually $hle) =>
      pure (u, some (true, hle))
    | _ => throwUnsupportedSyntax
  if let some (eventually, hle) := bound? then
    applyBound eventually hle
  if (← getUnsolvedGoals).isEmpty then return
  if let some u := unfolds? then
    let `(neglUnfolds| [$ids,*]) := u | throwUnsupportedSyntax
    let simpTerms ← ids.getElems.mapM fun id => `(Parser.Tactic.simpLemma| $id:ident)
    evalTactic (← `(tactic| simp only [$simpTerms,*]))
  if (← getUnsolvedGoals).isEmpty then return
  prepareNegligibleContext
  if (← getUnsolvedGoals).isEmpty then return
  normalizeNegligibleForms
  if (← getUnsolvedGoals).isEmpty then return
  abstractNegligibleHypotheses
  if (← getUnsolvedGoals).isEmpty then return
  let residualGoal ← getMainGoal
  try
    evalTactic (← `(tactic|
      solve | fun_prop (disch :=
        first
        | assumption
        | norm_num
        | positivity
        | omega
        | (intro n; first | assumption | omega | positivity | norm_num))))
  catch ex =>
    let residualTy ← residualGoal.withContext do instantiateMVars (← residualGoal.getType)
    throwError "negligible: `fun_prop` could not close the normalized goal:\
      {indentExpr residualTy}\n\
      Supply missing `Negligible` or `PolynomiallyBounded` hypotheses in context, or pass an \
      explicit upper bound with `negligible using hle` / `negligible eventually hle`.\n\
      {ex.toMessageData}"

end Cslib.Tactic.Negligible

end
