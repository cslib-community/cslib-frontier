/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
public import CslibFrontier.Tactic.FailureNote
public import CslibFrontier.Tactic.CertificatePreparation
public import CslibFrontier.Tactic.LogSpace.Init
public import CslibFrontier.Tactic.PolyTime.Init

/-!
# Synthesizing bounded logspace computations

`logspace` combines the existing plain `fun_prop` calculus with bounded list construction.
A local hypothesis `∀ a, r a ≤ k` selects the constant bound in the existing bounded-map rules;
it can also be specialized to a prepared argument such as `r p.1`. A constant count needs no
extra reflexive bound hypothesis. Both raw bit vectors (`encBits`) and framed lists
(`encList encOut`) retain their exact callback encoding, including unary indices. This does not
claim arbitrary polynomially long answer vectors are logspace computable.

`logspace [f, g]` unfolds only the named program definitions before search. Every form also
inlines local encoding `let`s and exposes the certificates stored in local structures, as
`polytime`, `ppt` and `space` do.

Named `program_certificate` proofs are tried before their implementations unfold. Local routine
certificates use recomputing logspace composition, including calls
on prepared tuple arguments. Search stays in `ComputableInLogSpace`: it never converts a goal
to polynomial time or to a tidy predicate. Importing this module adds no `fun_prop` transition.
When the search fails, its error ends with a note naming the certificates and bounds to supply.

## Main definitions

* `logspace`: close a plain logspace goal using local bounds, routine certificates and composition.
-/

public section

namespace Cslib.Tactic.LogSpace

open Turing.MultiTapeTM Lean Meta Elab Tactic

namespace Internal

/-- Curried callbacks let unification determine the indexed program from a map body.
This kernel declaration is public because runtime tactic application uses ordinary imports. -/
theorem mapToBitsRange {α : Type} {enc : α ↪ List Bool}
    {r : α → ℕ} {f : α → ℕ → Bool} (k : ℕ)
    (hr : ComputableInLogSpace r enc encUnary) (hrk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace (fun p : α × ℕ => f p.1 p.2)
      (encPair enc encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (r a)).map (f a)) enc encBits :=
  ComputableInLogSpace.mapToBits_range_of_le k hr hrk hf

/-- The framed-list counterpart of `mapToBitsRange`, with the element encoding fixed by the
result. Curried callbacks expose the two input components to unification. -/
theorem mapRange {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {r : α → ℕ} {f : α → ℕ → β} (k : ℕ)
    (hr : ComputableInLogSpace r enc encUnary) (hrk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace (fun p : α × ℕ => f p.1 p.2)
      (encPair enc encUnary) encOut) :
    ComputableInLogSpace (fun a => (List.range (r a)).map (f a)) enc (encList encOut) :=
  ComputableInLogSpace.map_range_of_le k hr hrk hf

end Internal

/-- Recognize the universal inequality shape expected by a bounded-map rule. -/
private meta def isBound (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs body =>
    pure (!xs.isEmpty && (body.isAppOf ``LE.le || body.isAppOf ``Nat.le))

/-- Specialize a supplied uniform bound to the goal's argument. Without a supplied bound, only
an input-independent count can choose its own reflexive bound. The bound metavariable lives
outside the input telescope, so unification cannot make it depend on the input. -/
private meta def closeBound (goal : MVarId) (bound : Option LocalDecl) : MetaM Unit :=
  goal.withContext do
    forallTelescopeReducing (← goal.getType) fun xs body => do
      let proof ← match bound with
        | some decl => do
          let (args, _, result) ← forallMetaTelescopeReducing decl.type
          unless ← isDefEq result body do throwError "bound does not match"
          let proof ← instantiateMVars (mkAppN decl.toExpr args)
          if proof.hasExprMVar then throwError "bound has undetermined premises"
          pure proof
        | none => do
          let args := body.getAppArgs
          let count ← whnfR args[args.size - 2]!
          if count.hasExprMVar || count.hasAnyFVar (xs.map (·.fvarId!) |>.contains) then
            throwError "count depends on the input"
          unless ← isDefEq args.back! count do throwError "constant bound does not match"
          mkAppM ``Nat.le_refl #[count]
      goal.assign (← mkLambdaFVars xs proof)

/-- Preserve every matching bound and output representation as a separate search alternative.
The same bounded-map contract constructs raw bits or framed elements; no encoding is guessed. -/
@[aesop unsafe 90% tactic (rule_sets := [LogSpace])]
private meta def boundedAnswers : Aesop.RuleTac := fun input => input.goal.withContext do
  let target := (← instantiateMVars (← input.goal.getType)).consumeMData
  unless target.isAppOf ``ComputableInLogSpace do throwError "expected a logspace goal"
  let mut bounds : Array (Option LocalDecl) := #[none]
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && (← isBound decl.type) then
      bounds := bounds.push (some decl)
  let initial ← saveState
  let mut applications := #[]
  for rule in [``Internal.mapToBitsRange, ``Internal.mapRange] do
    for bound in bounds do
      try
        let goals ← input.goal.applyConst rule
        let some boundGoal ← goals.findM? fun goal => do isBound (← goal.getType)
          | throwError "bounded-map rule has no bound premise"
        closeBound boundGoal bound
        let goals ← goals.filterM fun goal => return !(← goal.isAssigned)
        if ← Aesop.hasSorry (mkMVar input.goal) then throwError "admitted bound"
        let goals ← goals.toArray.mapM (Aesop.mvarIdToSubgoal input.goal)
        applications := applications.push {
          goals
          postState := ← saveState
          scriptSteps? := none
          successProbability? := none }
      catch _ => pure ()
      finally initial.restore
  if applications.isEmpty then throwError "no matching constant bound"
  return ⟨applications⟩

-- Expose tuple preparation when one component needs a bounded construction.
attribute [aesop unsafe 85% apply (rule_sets := [LogSpace])] ComputableInLogSpace.pair

/-- Reuse local routines before unfolding their implementation. -/
@[aesop unsafe 100% tactic (rule_sets := [LogSpace])]
private meta def knownCall : Aesop.RuleTac :=
  Cslib.Tactic.applyKnownCall ``ComputableInLogSpace 2 ``ComputableInLogSpace.comp `f `hg

/-- Try named logspace certificates without unfolding their implementations. -/
@[aesop unsafe 99% tactic (rule_sets := [LogSpace])]
private meta def namedCertificate : Aesop.RuleTac :=
  Cslib.Tactic.applyCertificates ``ComputableInLogSpace

/-- Composition closes ordinary leaves; bounded construction is a separate alternative. -/
@[aesop unsafe 95% tactic (rule_sets := [LogSpace])]
private meta def compositional : TacticM Unit := withMainContext do
  unless (← getMainTarget).isAppOf ``ComputableInLogSpace do
    throwError "expected a logspace goal"
  Term.withoutErrToSorry <| withoutRecover do
    evalTactic (← `(tactic| solve | fun_prop (config := { maxSteps := 256 })))

end Cslib.Tactic.LogSpace

/-- Prove a plain logspace certificate using composition and supplied constant bounds.
The optional names unfold program definitions before shared certificate preparation. -/
syntax (name := logspaceTactic) "logspace" (" [" ident,* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| logspace $[[$defs,*]]?) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``Turing.MultiTapeTM.ComputableInLogSpace do
      throwError "logspace expects a goal `ComputableInLogSpace f encIn encOut`, \
        got{indentExpr target}"
    Cslib.Tactic.prepareCertificateGoal ((defs.map (·.getElems)).getD #[])
    Cslib.Tactic.withFailureNote m!"logspace composes `@[fun_prop]` rules and named \
        `program_certificate`s for `ComputableInLogSpace`. Supply a certificate for each local \
        routine, with the goal's encodings, or unfold a definition with `logspace [f]`. \
        A list `(List.range (r a)).map (f a)` also needs a constant count or a hypothesis \
        `∀ a, r a ≤ k`." do
      evalTactic (← `(tactic| solve |
        aesop
          (config :=
            { terminal := true
              enableSimp := false
              assumptionTransparency := .reducible })
          (rule_sets := [LogSpace])))

end
