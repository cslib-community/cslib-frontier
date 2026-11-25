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

`logspace` combines the existing plain `fun_prop` calculus with bounded answer-vector
construction. A local hypothesis `∀ a, r a ≤ k` selects the constant bound in
`ComputableInLogSpace.mapToBits_range_of_le`, also for a count taken at a prepared argument such
as `r p.1`; the count and indexed callback still need their own certificates with the exact
input and output encodings. In particular, this rule does not claim arbitrary polynomially long
answer vectors are logspace computable.

`logspace [f, g]` first unfolds `f` and then `g` in the goal, as `unfold f g` does, so a name
that does not occur at its turn is an error. Every form then runs the preparation shared with
`polytime`, `ppt` and `space` (`Cslib.Tactic.prepareCertificateGoal`): it inlines literal `let`s
in the goal and local encoding `let`s, and adds the certificates stored in local structures as
local facts.

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

end Internal

/-- Whether a type is a universally quantified inequality, the shape of a count bound. -/
private meta def isBound (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs body => pure (!xs.isEmpty && body.isAppOf ``LE.le)

/-- Close the bound premise `goal` of the bounded-map rule with the supplied uniform bound,
either as stated or specialized to the goal's argument. The constant of the rule is a
metavariable created outside the input telescope, so unification cannot make it depend on the
input. -/
private meta def closeBound (goal : MVarId) (bound : LocalDecl) : MetaM Unit :=
  goal.withContext do
    if ← isDefEq (← goal.getType) bound.type then
      goal.assign bound.toExpr
      return
    forallTelescopeReducing (← goal.getType) fun xs body => do
      let (args, _, result) ← forallMetaTelescopeReducing bound.type
      unless ← isDefEq result body do throwError "bound does not match"
      let proof ← instantiateMVars (mkAppN bound.toExpr args)
      if proof.hasExprMVar then throwError "bound has undetermined premises"
      goal.assign (← mkLambdaFVars xs proof)

/-- Preserve each matching supplied bound as a separate search alternative. Selecting the bound
first determines the count function and constant without guessing either from a data goal. -/
@[aesop unsafe 90% tactic (rule_sets := [LogSpace])]
private meta def boundedAnswers : Aesop.RuleTac := fun input => input.goal.withContext do
  let target := (← instantiateMVars (← input.goal.getType)).consumeMData
  unless target.isAppOf ``ComputableInLogSpace do throwError "expected a logspace goal"
  let initial ← saveState
  let mut applications := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless ← isBound decl.type do continue
    try
      let goals ← input.goal.applyConst ``Internal.mapToBitsRange
      let some boundGoal ← goals.findM? fun goal => do isBound (← goal.getType)
        | throwError "bound does not match"
      closeBound boundGoal decl
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

`logspace [f, g]` first unfolds `f` and then `g` in the goal, as `unfold f g` does; a name that
does not occur at its turn is an error. Before searching, every form also inlines literal `let`s
in the goal, replaces local encoding `let`s by their values and adds the certificates stored in
fields of local structures as local facts, as `polytime` does. -/
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
        An answer vector `(List.range (r a)).map (f a)` also needs a hypothesis \
        `∀ a, r a ≤ k`." do
      evalTactic (← `(tactic| solve |
        aesop (config := { terminal := true, enableSimp := false })
          (rule_sets := [LogSpace])))

end
