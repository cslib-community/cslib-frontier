/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.BoundedWalk.Runtime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally

/-!
# Membership tallies with a runtime bounded walk

A tally can call a bounded-walk machine whose transition rules read the dimension from the
walk state. Each call enters at the tally's dimension, source, candidate and radius. This
allows different tally queries to use the same walk on the original input.

## Main definitions

* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk`: the existing membership tally
  using a walk with runtime dimensions.

## Main results

* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_firstHalting_iff`: a successful
  first-halt selector list describes exactly one successful typed scan with the same reply.
* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_haltsWithin` and
  `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_length_run_le`: the common selector
  clock and encoded-state bound for all branches starting from a valid source.
-/

public section

namespace Turing.DoubleCounting.MembershipTally

open Cslib.DoubleCounting
open Turing.DoubleCounting.BoundedWalk

variable {κ τ : Type} (edge : QueryMachine τ) (start : κ → ℕ → ℕ → τ)
  (verdict : τ → Bool) (clock : ℕ)

private def enterRuntimeWalk (context : κ) (r : Registers) : Runtime.State κ τ :=
  if h : r.context.source < r.context.size ∧ r.cursor < r.context.size then
    Runtime.entry edge start verdict clock context
      ⟨⟨r.context.source, h.1⟩, ⟨r.cursor, h.2⟩, r.context.radius⟩
  else ⟨context, 1, Nat.zero_lt_one, .done none⟩

variable (initialWalk : Runtime.State κ τ) (context : κ)

/-- Run a membership tally with the supplied runtime walk. The walk enters at each valid
candidate with the tally's dimension and supplied adjacency context. An invalid walk entry
rejects. -/
def withRuntimeWalk (ctx : Context) : NondeterministicQueryMachine (State (Runtime.State κ τ)) :=
  machine ctx (Runtime.machine edge start verdict clock initialWalk)
    (enterRuntimeWalk edge start verdict clock context) Runtime.remainingFuel

/-- Re-enter the tally at new query parameters using the same runtime walk and adjacency context. -/
theorem withRuntimeWalk_withInit (ctx newContext : Context) :
    (withRuntimeWalk edge start verdict clock initialWalk context ctx).withInit
      (initial newContext) =
    withRuntimeWalk edge start verdict clock initialWalk context newContext := by
  unfold withRuntimeWalk NondeterministicQueryMachine.withInit
  rfl

/-- A successful first halt has exactly the selectors of a unique successful typed scan
and preserves its membership bit. The walk's original entry can have a different dimension
and adjacency context. -/
theorem withRuntimeWalk_firstHalting_iff {N : ℕ} (input : List Bool)
    (adjacent : Fin N → Fin N → Bool) (source target : Fin N) (radius : ℕ)
    (expected : Tally)
    (hclock : ∀ u v : Fin N,
      edge.halted (edge.runFrom input (start context u.val v.val) clock) = true)
    (hedge : ∀ u v : Fin N,
      verdict (edge.runFrom input (start context u.val v.val) clock) = adjacent u v)
    (bits : List Bool) (hit : Bool) :
    let M := withRuntimeWalk edge start verdict clock initialWalk context
      ⟨N, source.val, target.val, radius, expected⟩
    M.FirstHalting input bits M.init ∧ reply (M.run input bits) = some hit ↔
      ∃! branch, bits = selectors (BoundedWalk.selectors clock) branch ∧
        Scan.run adjacent source target radius expected branch = some hit := by
  unfold withRuntimeWalk
  refine firstHalting_iff_scan _ _ _ input adjacent source target radius expected
    (BoundedWalk.selectors clock) (BoundedWalk.eq_of_selectors_prefix clock) ?_ bits hit
  intro v acc ws left
  simpa only [enterRuntimeWalk, source.isLt, v.isLt, and_self, dite_true] using
    Runtime.firstHalting_remainingFuel_iff edge start verdict clock initialWalk context
      ⟨source, v, radius⟩ input adjacent hclock hedge ws left

private theorem runtimeWalk_withInit {ctx : Context} (r : Registers) (hr : r.context = ctx)
    (hsource : ctx.source < ctx.size) (hcursor : r.cursor < ctx.size) :
    let entry := Runtime.entry edge start verdict clock context
      ⟨⟨ctx.source, hsource⟩, ⟨r.cursor, hcursor⟩, ctx.radius⟩
    (Runtime.machine edge start verdict clock initialWalk).withInit
      (enterRuntimeWalk edge start verdict clock context r) =
    Runtime.machine edge start verdict clock entry := by
  cases hr
  simp only [Runtime.machine_withInit, enterRuntimeWalk, dite_eq_left (And.intro hsource hcursor)]

/-- Charge the candidate scan and its calls, including all rejecting selector lists. -/
theorem withRuntimeWalk_haltsWithin (ctx : Context) (hsource : ctx.source < ctx.size)
    (input : List Bool) :
    (withRuntimeWalk edge start verdict clock initialWalk context ctx).HaltsWithin input
      (ctx.size * (ctx.radius * (ctx.size.size + clock + 3) + (ctx.size.size + 2) + 2) + 1) := by
  apply haltsWithin
  intro r hr _ hcursor
  rw [runtimeWalk_withInit edge start verdict clock initialWalk context r hr hsource hcursor]
  exact Runtime.haltsWithin edge start verdict clock context
    ⟨⟨ctx.source, hsource⟩, ⟨r.cursor, hcursor⟩, ctx.radius⟩ input

/-- Add the framed adjacency context and runtime dimension to the fixed-dimension tally bound. -/
@[expose] def runtimeWalkStateBound (clock : ℕ) (ctx : Context)
    (contextLength calleeBound : ℕ) : ℕ :=
  stateBound ctx (Runtime.stateBound ctx.size ctx.radius clock contextLength calleeBound)

/-- Bound the encoded tally state on every selector prefix, including while a walk retains
the adjacency context and a suspended callback state. -/
theorem withRuntimeWalk_length_run_le (encK : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    (ctx : Context) (hsource : ctx.source < ctx.size) (input : List Bool) (calleeBound : ℕ)
    (hcallee : ∀ u v : Fin ctx.size, ∀ t ≤ clock,
      (encCallee (edge.runFrom input (start context u.val v.val) t)).length ≤ calleeBound)
    (bits : List Bool) :
    (encState (Runtime.encState encK encCallee)
      ((withRuntimeWalk edge start verdict clock initialWalk context ctx).run input bits)).length ≤
      runtimeWalkStateBound clock ctx (encK context).length calleeBound := by
  unfold runtimeWalkStateBound
  apply length_replay_le
  intro r hr _ hcursor choices
  rw [← NondeterministicQueryMachine.run_withInit,
    runtimeWalk_withInit edge start verdict clock initialWalk context r hr hsource hcursor]
  exact Runtime.length_run_le edge start verdict clock context
    ⟨⟨ctx.source, hsource⟩, ⟨r.cursor, hcursor⟩, ctx.radius⟩ input choices
    encK encCallee calleeBound hcallee

end Turing.DoubleCounting.MembershipTally
