/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TailCall
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointAncestry

/-!
# Checking descendant requests with a finite tail-call controller

The newest split is removed first. Its verified local segment either halts or prepares a
request for the previous ancestry on the tapes before jumping back to the same entry. This
interface separates constructing the local segment and its root implementation from composing
them uniformly over runtime ancestry. Accepted claims concern the actual numbered child edges.
-/

public section

namespace Turing.MultiTapeATM.DescendantEndpointLoop

open MultiTapeTM MultiTapePTM Cslib.Circuits.Frontier NativeChild EndpointQuery

/-- A logical stack in newest-first order describes the endpoint semantics at its top. -/
noncomputable def atStack (root : EndpointQuery) (stack : List Labels) : EndpointQuery :=
  stack.foldr (fun l q => q.child (l.split q)) root

/-- Applying the tail-call theorem to the endpoint verifier gives a machine that is uniform
in the depth, with branch time equal to the sum of the local budgets and one final root lookup.
The hypotheses refer to concrete tape configurations of one controller. -/
theorem run {k u copies q : ℕ} {R S : Type}
    (source : MultiTapePTM k Bool R) (word : List Bool) (b σ : ℕ)
    (code : BlockLetter k R b → Fin copies → Bool) (body : MultiTapeATM u Bool S) (again : S → Bool)
    {input : List Bool} (read : Cfg u Bool S input → ℕ × (ℕ × ℕ))
    (ready : List Labels → Cfg u Bool S input → Prop) (cost : Labels → ℕ) (rootTime : ℕ) :
    let raw := ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ))
    let root := RootEndpointQuery.endpointQuery k copies raw
    let meaning (stack : List Labels) (z : Cfg u Bool S input) :=
      (atStack root stack).accepts (read z).1 (read z).2
    let atm := TailCall.machine body again
    (∀ z, ready [] z → atm.HaltsWithin rootTime z ∧ (atm.AcceptsWithin rootTime z ↔
      RootEndpointQuery.query k ⟨raw, copies, (read z).1⟩ = some (read z).2)) →
    (∀ l ls z, ready (l :: ls) z → TailCall.Segment body again (ready ls) (meaning ls)
      (cost l) z (meaning (l :: ls) z)) →
    ∀ stack z, ready stack z →
      let time := stack.foldr (fun l t => cost l + 1 + t) rootTime
      let edges := stack.foldr (fun l es => l.edges es) (RootPortGraph.ends (q := q)
        source word b σ code)
      atm.HaltsWithin time z ∧ (atm.AcceptsWithin time z ↔
        (read z).1 < edges.length ∧ edges.getD (read z).1 (0, 0) = (read z).2) := by
  intro raw root meaning atm hbase hstep stack z hz
  have hrun := TailCall.run_levels body again cost rootTime ready meaning hbase hstep stack z hz
  have hrep := RootEndpointQuery.represents_descendant (q := q) source word b σ code stack.reverse
  dsimp only at hrep
  simp only [List.foldl_reverse] at hrep
  exact ⟨hrun.1, hrun.2.trans (hrep.2 _ _)⟩

end Turing.MultiTapeATM.DescendantEndpointLoop
