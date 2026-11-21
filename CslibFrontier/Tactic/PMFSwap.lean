/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.BindChain
public meta import Lean.Elab.Tactic.Location

/-!
# Reordering independent samples

Two probabilistic experiments that draw the same independent samples in different orders have
the same law, by `PMF.bind_comm`. Proving such an equation by rewriting means navigating to each
swap (`conv_lhs => enter [2, a, 2, b]`) and stripping the common samples one at a time
(`congr 1 with x : 1`), and `simp [PMF.bind_comm]` loops on two samples of the same distribution.
The tactics here match samples by their distributions instead of their positions.

`pmf_swap` proves an equation `lhs = rhs` of distributions whose sides are sampling chains.
It normalizes visible monadic notation, nested binds, maps, and `ProbComp.eval` before matching;
named program bodies stay opaque until explicitly unfolded.
It brings a sample of the right side that the left side draws independently of its earlier samples
to the front of both sides, by `PMF.bind_comm`, strips it, and continues with the continuations.
Samples of the same distribution may be matched in any order: the tactic searches for an order in
which the two sides become equal up to reducible unfolding, and then closes the goal. The search
has a budget, renewed after stripping each sample with a single possible partner, and the tactic
fails when it runs out. If no order works, it strips common samples and leaves the equation of the
remaining continuations, with the stripped samples as variables, unless `rfl` proves it. It first
strips samples whose distribution occurs once on each side, which have only one possible partner,
and then the first matches of the others. `pmf_swap with x y` skips the search and strips exactly
two samples, naming them in the order they occur in the right side; plain `pmf_swap` strips every
sample it can. It fails when it can strip no sample, listing the samples of both sides and marking
those that depend on earlier ones, which cannot move. `pmf_swap [h]` also moves samples past a
sampler `F`, a function of a continuation, given a commutation lemma
`h : μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)`.

`pmf_hoist q` moves every sample of the distribution `q` in the goal, or in a hypothesis with
`at h`, as far toward the front of its chain as its independence allows. It works anywhere in the
goal, for instance inside a probability or an inequality, where `pmf_swap` does not apply.
`pmf_hoist (occ := n) q` moves only the `n`th sample of `q`, for chains that draw `q` more than
once. `pmf_hoist [h] F` also moves a custom sampler `F` using the same commutation rule as
`pmf_swap [h]`.

Distributions are compared up to reducible unfolding. A sample of a distribution that depends
on an earlier sample never moves past that sample.

## Main definitions

* `pmf_swap`: prove an equation of distributions that differ in the order of independent samples.
* `pmf_hoist`: move the samples of a given distribution to the front of their chains.
-/

public meta section

namespace Cslib.Tactic.PMFSwap

open Lean Meta Elab Tactic

open BindChain

/-- An alignment of `lhs = rhs`: a sample `q` drawn independently at depth `kl` of `lhs` and at
depth `kr` of `rhs`. -/
private abbrev Alignment := Pat × Nat × Nat

/-- The ways to bring one sample to the front of both sides of `lhs = rhs`: the first sample of
`rhs` matched with each of its occurrences in `lhs`, and failing that the first sample of `lhs`
matched with each of its occurrences in `rhs`. Every proof by reordering matches the first sample
of `rhs` with some sample of `lhs`, so `search` loses nothing by trying only these. -/
private def alignments (ctx : BindChain.Context) (lhs rhs : Expr) : MetaM (Array Alignment) := do
  if let some s ← sample? ctx rhs then
    let ks ← findDepths ctx s.toPat lhs
    unless ks.isEmpty do return ks.map ((s.toPat, ·, 0))
  if let some s ← sample? ctx lhs then
    return (← findDepths ctx s.toPat rhs).map ((s.toPat, 0, ·))
  return #[]

/-- The samples of the chain `e` that do not depend on earlier samples. -/
private partial def independentHeads (ctx : BindChain.Context) (e : Expr)
    (earlier : Array Expr := #[]) : MetaM (Array Pat) := do
  let some s ← sample? ctx e | return #[]
  let dep := earlier.any fun x => s.head.containsFVar x.fvarId!
  let rest ← withBody s.cont fun x body => independentHeads ctx body (earlier.push x)
  return if dep then rest else #[s.toPat] ++ rest

/-- A forced alignment of `lhs = rhs`: a sample of `rhs` whose distribution occurs exactly once on
each side, so that it has a single possible partner. -/
private def forced? (ctx : BindChain.Context) (lhs rhs : Expr) : MetaM (Option Alignment) := do
  for q in ← independentHeads ctx rhs do
    let kls ← findDepths ctx q lhs
    let krs ← findDepths ctx q rhs
    if let (#[kl], #[kr]) := (kls, krs) then return some (q, kl, kr)
  return none

/-- Carry out an alignment `(q, kl, kr)` of `lhs = rhs`: the continuations `f` and `g` and proofs
of `lhs = q.front f` and `rhs = q.front g`. -/
private def realize (ctx : BindChain.Context) (lhs rhs : Expr) :
    Alignment → MetaM (Pat × Expr × Expr × Expr × Expr)
  | (q, kl, kr) => do
    let (lhs', hl) ← hoistAt ctx q lhs kl
    let (rhs', hr) ← hoistAt ctx q rhs kr
    return (q, lhs'.appArg!, rhs'.appArg!, hl, hr)

/-- A proof of `lhs = rhs` from `hl : lhs = q.front f`, `hr : rhs = q.front g` and `h : f = g`. -/
private def combine (lhs rhs : Expr) (q : Pat) (f hl hr h : Expr) : MetaM Expr := do
  let hmid ← stepCongr q f h
  let pf ← mkEqTrans (← mkEqTrans hl hmid) (← mkEqSymm hr)
  mkExpectedTypeHint pf (← mkEq lhs rhs)

/-- The number of steps of `search` for the goal and again after each forced alignment. -/
private def searchBudget : Nat := 256

/-- Search for a proof of `lhs = rhs` that aligns the samples of the two sides until the remaining
continuations are reducibly equal, trying every matching sample of the other side. Each call
spends one unit of `fuel`; when `fuel` reaches zero the search gives up, so `none` with no fuel
left means that the budget ran out, not that no matching exists. An alignment that a commutation
lemma does not prove is skipped. -/
private partial def search (ctx : BindChain.Context) (fuel : IO.Ref Nat) (lhs rhs : Expr) :
    MetaM (Option Expr) := do
  if (← fuel.get) == 0 then return none
  fuel.modify (· - 1)
  if ← withNewMCtxDepth <| withReducible <| isDefEq lhs rhs then
    return some (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
  for a in ← alignments ctx lhs rhs do
    let some (q, f, g, hl, hr) ←
        if ctx.comms.isEmpty && ctx.swapSamplers?.isNone then some <$> realize ctx lhs rhs a
        else observing? (realize ctx lhs rhs a) | continue
    let h? ← withBody f fun x fx => do
      let some h ← search ctx fuel fx (g.beta #[x]) | return none
      return some (← mkLambdaFVars #[x] h)
    if let some h := h? then
      return some (← combine lhs rhs q f hl hr (← mkFunExt h))
  return none

/-- Strip one common sample from both sides of the goal `lhs = rhs` and introduce it as an
inaccessible variable. A forced alignment comes first; otherwise, unless `forcedOnly`, the first
sample of `rhs` that `lhs` also draws. Returns the variable, its depth in `rhs` and the new goal,
or `none` when no sample can be aligned. -/
private def peel? (ctx : BindChain.Context) (goal : MVarId) (forcedOnly := false) :
    MetaM (Option (FVarId × Nat × MVarId)) :=
  goal.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← goal.getType)).cleanupAnnotations.eq?
      | return none
    let some a ← (do
        if let some a ← forced? ctx lhs rhs then return some a
        if forcedOnly then return none
        return (← alignments ctx lhs rhs)[0]?) | return none
    let (q, f, g, hl, hr) ← realize ctx lhs rhs a
    let ty ← withBody f fun x fx => do mkForallFVars #[x] (← mkEq fx (g.beta #[x]))
    let m ← mkFreshExprSyntheticOpaqueMVar ty (← goal.getTag)
    goal.assign (← combine lhs rhs q f hl hr (← mkFunExt m))
    let (x, goal') ← m.mvarId!.intro1
    return some (x, a.2.2, goal')

/-- The outcome of trying to close a goal by `search`. -/
private inductive Closed where
  /-- The goal is closed. -/
  | closed
  /-- No order of the samples makes the two sides equal. -/
  | noMatching
  /-- The budget ran out, and no remaining sample has a single possible partner. -/
  | outOfBudget

/-- Close the goal `g` by `search`. When the budget runs out, strip a sample with a single possible
partner, which every matching aligns the same way, and search the rest with a fresh budget. -/
private partial def closeGo (ctx : BindChain.Context) (g : MVarId) :
    MetaM Closed := g.withContext do
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).cleanupAnnotations.eq?
    | return .noMatching
  let fuel ← IO.mkRef searchBudget
  if let some pf ← search ctx fuel lhs rhs then
    g.assign pf
    return .closed
  if (← fuel.get) != 0 then return .noMatching
  let some (_, _, g') ← peel? ctx g (forcedOnly := true) | return .outOfBudget
  closeGo ctx g'

/-- Close the goal by `search`, as `closeGo`, assigning it only when it is closed. -/
private def close (ctx : BindChain.Context) (goal : MVarId) : MetaM Closed := do
  let s ← saveState
  let r ← closeGo ctx goal
  unless r matches .closed do s.restore
  return r

/-- The samples of the chain `e`, each marked when it depends on an earlier sample. -/
private partial def chainMsgs (ctx : BindChain.Context) (e : Expr) (earlier : Array Expr := #[]) :
    MetaM (Array MessageData) := do
  let some s ← sample? ctx e | return #[]
  let dep := earlier.any fun x => s.head.containsFVar x.fvarId!
  let msg ← addMessageContext
    m!"{s.head}{if dep then " (depends on an earlier sample)" else ""}"
  let rest ← withBody s.cont fun x body => chainMsgs ctx body (earlier.push x)
  return #[msg] ++ rest

/-- The error when `pmf_swap` can strip no sample from `lhs = rhs`. -/
private def noCommonSample (ctx : BindChain.Context) (lhs rhs : Expr) : MetaM MessageData := do
  let ls ← chainMsgs ctx lhs
  let rs ← chainMsgs ctx rhs
  if ls.isEmpty || rs.isEmpty then
    return m!"pmf_swap: both sides must expose sampling chains; unfold named programs or provide \
      sampler commutation lemmas.\nLeft side:{indentExpr lhs}\nRight side:{indentExpr rhs}"
  let list (ms : Array MessageData) := indentD (MessageData.joinSep ms.toList Format.line)
  return m!"pmf_swap: the two sides have no independent sample in common.\n\
    Left side samples:{list ls}\nRight side samples:{list rs}\n\
    A sample can move to the front only when its distribution does not depend on earlier samples."

/-- The position in the original right side of the sample at depth `k` of the right side after
the samples at the positions `stripped` have been removed. -/
private def origPos (stripped : Array Nat) (k : Nat) : Nat := Id.run do
  let mut seen := 0
  for i in [0:k + stripped.size + 1] do
    if stripped.contains i then continue
    if seen == k then return i
    seen := seen + 1
  return k + stripped.size

/-- `pmf_swap` proves an equation `lhs = rhs` of distributions whose sides draw the same
independent samples in different orders. Visible monadic notation, nested binds, maps, and
`ProbComp.eval` are normalized automatically, without unfolding named programs. The tactic brings
a sample that both sides draw independently of their earlier samples to the front of both, by
`PMF.bind_comm`, strips it, and continues. Samples are
matched by their distributions, up to reducible unfolding, not by position.

If the samples can be matched so that the two sides become equal, up to reducible unfolding, the
goal is closed; samples of the same distribution are tried in every order. The search has a budget
of 256 steps, renewed after stripping each sample whose distribution occurs once on each side, and
the tactic fails when the budget runs out with no such sample left. If no order makes the sides
equal, `pmf_swap` strips common samples and leaves the equation of what remains, with the
stripped samples as variables: first the samples whose distribution occurs once on each side, then
the first match of each remaining sample of the right side, and fails when it can strip none. It
closes the remaining equation when `rfl` proves it.

`pmf_swap with x y` skips the search and strips exactly two samples in the same way, and fails if
it cannot. The names follow the order of the samples in the right side, whatever order they are
stripped in: on `(p.bind fun a => q.bind fun b => f a b) = q.bind fun b => p.bind fun a => g a b`,
`pmf_swap with y x` leaves `f x y = g x y`. The remaining equation is left as it is.

`pmf_swap [h₁, h₂]` also moves samples past a sampler `F`, a function of a continuation such as
`Game.runStatelessOracle o prog`, given commutation lemmas of the form
`h : μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)` for every distribution `μ`.
An application `F k` is then a sample of `F` with continuation `k`. Two samplers do not move past
each other. -/
syntax (name := pmfSwap) "pmf_swap" (" [" term,* "]")? (" with" (ppSpace colGt binderIdent)+)? :
  tactic

@[inherit_doc pmfSwap]
elab_rules : tactic
  | `(tactic| pmf_swap $[[$hs,*]]? $[with $xs*]?) => do
    let ctx : BindChain.Context :=
      { comms := ← ((hs.map (·.getElems)).getD #[]).mapM fun h => elabComm h }
    let names : Array (Option Name) := (xs.getD #[]).map fun
      | `(binderIdent| $n:ident) => some n.getId
      | _ => none
    let goal ← getMainGoal
    goal.withContext do
      let target := (← instantiateMVars (← goal.getType)).cleanupAnnotations
      let some (ty, lhs, rhs) := target.eq?
        | throwError "pmf_swap: the goal is not an equation of distributions{indentExpr target}"
      unless (← whnfR ty).isAppOf ``PMF do
        throwError "pmf_swap: the goal is an equation in{indentExpr ty}\n\
          not an equation of distributions `PMF α`"
      let (lhs, hl?) ← normalize ctx lhs
      let (rhs, hr?) ← normalize ctx rhs
      let goal ← if hl?.isSome || hr?.isSome then do
          let next ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs rhs) (← goal.getTag)
          let hl ← match hl? with | some h => pure h | none => mkEqRefl lhs
          let hr ← match hr? with | some h => pure h | none => mkEqRefl rhs
          goal.assign (← mkEqTrans hl (← mkEqTrans next (← mkEqSymm hr)))
          pure next.mvarId!
        else pure goal
      if names.isEmpty then
        match ← close ctx goal with
        | .closed => replaceMainGoal []; return
        | .outOfBudget => throwError "pmf_swap: the search for an order of the samples ran out \
            of its budget of {searchBudget} steps.\nStrip samples with `pmf_swap with x …`, or \
            reorder them with `pmf_hoist` or `PMF.bind_comm`, to leave fewer samples to match."
        | .noMatching => pure ()
      let mut g := goal
      -- The stripped samples and their positions in the original right side.
      let mut stripped : Array (FVarId × Nat) := #[]
      repeat
        if !names.isEmpty && stripped.size == names.size then break
        let some (x, kr, g') ← peel? ctx g | break
        stripped := stripped.push (x, origPos (stripped.map (·.2)) kr)
        g := g'
      if stripped.isEmpty then throwError (← noCommonSample ctx lhs rhs)
      for (x, _) in stripped.qsort (·.2 < ·.2), n? in names do
        if let some n := n? then g ← g.rename x n
      if stripped.size < names.size then
        g.withContext do
          throwError "pmf_swap: only {stripped.size} of the {names.size} named samples can be \
            stripped; what remains is{indentExpr (← instantiateMVars (← g.getType))}"
      if names.isEmpty then
        let s ← saveState
        try
          g.refl
          replaceMainGoal []
          return
        catch _ => s.restore
      replaceMainGoal [g]

/-- An occurrence `(occ := n)` of a distribution, counted from 1. -/
syntax pmfHoistOcc := atomic("(" &"occ") " := " num ")"

/-- `pmf_hoist q` moves every sample of the distribution `q`, in every chain of `PMF.bind` in the
goal, as far toward the front of its chain as possible, by `PMF.bind_comm`: past every earlier
sample, which `q` cannot depend on. `q` may contain holes `_`, which are filled by its first match.
Like `rw`, it then closes a goal that has become reflexive. `pmf_hoist q at h` works on the
hypothesis `h` instead. It fails when no sample of `q` moves.

`pmf_hoist (occ := n) q` moves only the `n`th independent sample of `q`, counting from the front of
each chain and through the chains in the order they occur, the left side of an equation before the
right. When a chain draws `q` twice, it chooses which of the two `pmf_swap` or `congr 1 with x : 1`
then pairs with the first sample of the other side. It fails when that sample is already at the
front of its chain or there are fewer than `n` independent samples of `q`.

`pmf_hoist [h] F` also moves a custom sampler `F`, such as `Game.runStatelessOracle o prog`,
given a commutation rule of the form accepted by `pmf_swap [h]`. The same rule lets a distribution
move past `F`; two custom samplers do not move past each other. Visible monadic chains are
normalized before selecting the sample. -/
syntax (name := pmfHoist) "pmf_hoist " ("[" term,* "]" ppSpace)? (pmfHoistOcc ppSpace)? term
  (Lean.Parser.Tactic.location)? : tactic

@[inherit_doc pmfHoist]
elab_rules : tactic
  | `(tactic| pmf_hoist $[[$hs,*]]? $[(occ := $n?)]? $qStx $[$loc]?) => withMainContext do
    let ctx : BindChain.Context :=
      { comms := ← ((hs.map (·.getElems)).getD #[]).mapM fun h => elabComm h }
    let occ? := n?.map (·.getNat)
    if occ? == some 0 then throwError "pmf_hoist: occurrences are counted from 1"
    let q ← instantiateMVars (← elabTerm qStx none (mayPostpone := true))
    let q ← if let some p ← samplerPat? ctx q then pure p else do
        discard <| outcomeType q
        pure { head := q }
    let hoisted ← IO.mkRef false
    -- With `occ`, the number of independent samples of `q` in the chains visited so far.
    let seen ← IO.mkRef 0
    let methods : Simp.Methods := {
      pre := fun e => do
        if occ?.isSome && (← hoisted.get) then return .done { expr := e }
        let (normalized, hNorm?) ← normalize ctx e
        let some k ← firstDepth? ctx q normalized | return .continue
        let q := { q with head := ← instantiateMVars q.head }
        let mut k := k
        if let some n := occ? then
          -- Count the samples of the whole chain here, and do not visit its subchains again.
          let ks ← findDepths ctx q normalized
          if ks.isEmpty then return .continue
          let before ← seen.get
          seen.set (before + ks.size)
          if before + ks.size < n then return .done { expr := e }
          k := ks[n - 1 - before]!
          if k == 0 then
            throwError "pmf_hoist: sample {n} of{indentExpr q.head}\nis already at the front \
              of its chain"
        if k == 0 then
          return if hNorm?.isSome then .visit { expr := normalized, proof? := hNorm? }
            else .continue
        let (e', pf) ← hoistAt ctx q normalized k
        hoisted.set true
        let r : Simp.Result := { expr := e', proof? := ← chainEqOpt e e' hNorm? (some pf) }
        return if occ?.isSome then .done r else .visit r }
    -- With `occ`, equal subterms are distinct occurrences, so simp must not memoize.
    let simpc ← Simp.mkContext
      { zeta := false, iota := false, proj := false, memoize := occ?.isNone }
    let run (e : Expr) : MetaM Simp.Result := do
      hoisted.set false
      seen.set 0
      let (r, _) ← Simp.main e simpc (methods := methods)
      unless ← hoisted.get do
        let q ← instantiateMVars q.head
        if let some n := occ? then
          throwError "pmf_hoist: there is no sample {n} of{indentExpr q}\n\
            the chains draw it independently {← seen.get} times"
        throwError "pmf_hoist: no sample of{indentExpr q}\ncan move toward the front of its chain"
      return r
    withLocation (expandOptLocation (mkOptionalNode loc))
      (atLocal := fun h => do
        let goal ← getMainGoal
        let r ← run (← instantiateMVars (← h.getType))
        match ← applySimpResultToLocalDecl goal h r false with
        | none => replaceMainGoal []
        | some (_, g) => replaceMainGoal [g])
      (atTarget := do
        let goal ← getMainGoal
        let target ← instantiateMVars (← goal.getType)
        let goal ← applySimpResultToTarget goal target (← run target)
        -- Like `rw`, close a goal that has become reflexive.
        try withReducible goal.refl; replaceMainGoal []
        catch _ => replaceMainGoal [goal])
      (failed := fun _ => throwError "pmf_hoist: no sample of{indentExpr q.head}\ncan move")

end Cslib.Tactic.PMFSwap
