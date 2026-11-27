/-
Copyright (c) 2026 OpenAI, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time prefix scans

First-match indices and taking or dropping an initial segment are polynomial-time, including
when the predicate captures the input. The first-match rule is extracted from the native edge-CSP
walk API; the prefix rule also serves its ancestry construction.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
  {xs : α → List β} {pred : α → β → Bool}

/-- Find the first matching position, in unary; if there is none, return the list length. -/
@[fun_prop] theorem findIdxWithInput
    (hx : ComputableInPolyTime xs enc (encList encB))
    (hp : ComputableInPolyTime (fun p : α × β => pred p.1 p.2) (encPair enc encB) encBool) :
    ComputableInPolyTime (fun a => (xs a).findIdx (pred a)) enc encUnary := by
  have h := (idxOf encBool).comp ((mapWithInput hx hp).prod (const true))
  simpa [List.idxOf, List.findIdx_map, Function.comp_def] using h

/-- Take the maximal prefix passing an input-dependent polynomial-time predicate. -/
@[fun_prop] theorem takeWhileWithInput
    (hx : ComputableInPolyTime xs enc (encList encB))
    (hp : ComputableInPolyTime (fun p : α × β => pred p.1 p.2) (encPair enc encB) encBool) :
    ComputableInPolyTime (fun a => (xs a).takeWhile (pred a)) enc (encList encB) := by
  have hn := findIdxWithInput (pred := fun a b => !(pred a b)) hx (by fun_prop)
  simpa only [List.takeWhile_eq_take_findIdx_not] using
    (ComputableInPolyTime.listTakeWithInput hx hn)

/-- Drop the maximal prefix passing an input-dependent polynomial-time predicate. -/
@[fun_prop] theorem dropWhileWithInput
    (hx : ComputableInPolyTime xs enc (encList encB))
    (hp : ComputableInPolyTime (fun p : α × β => pred p.1 p.2) (encPair enc encB) encBool) :
    ComputableInPolyTime (fun a => (xs a).dropWhile (pred a)) enc (encList encB) := by
  have hn := findIdxWithInput (pred := fun a b => !(pred a b)) hx (by fun_prop)
  simpa only [List.dropWhile_eq_drop_findIdx_not] using
    (ComputableInPolyTime.listDropWithInput hx hn)

end Turing.MultiTapeTM.ComputableInPolyTime
