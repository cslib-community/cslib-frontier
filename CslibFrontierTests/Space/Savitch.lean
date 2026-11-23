/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Reachability.Savitch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Foundations.Data.BitString.Counter

/-!
# Tests: Savitch's midpoint reachability

The midpoint recursion on a directed path through the words of width two, on a graph whose target
is unreachable, and on the trivial walk at depth zero; walks of the path through
`Cslib.Reachability.reach_iff`; and an instance of its polynomial-space certificate for a family of
depths, so that its hypotheses are satisfiable.
-/

namespace CslibFrontierTests.Savitch

open Cslib Cslib.Reachability Turing.MultiTapeTM

/-! ### A directed path -/

/-- The path `00 → 10 → 01 → 11` through the words of width two, in counter order. -/
private def path (u v : List Bool) : Bool :=
  !u.all id && decide (BitString.increment u = v)

-- At level `i`, the walks of at most `2 ^ i` steps along the directed path.
example :
    reach path 2 0 [false, false] [true, false] = true ∧
    reach path 2 0 [false, false] [false, true] = false ∧
    reach path 2 1 [false, false] [false, true] = true ∧
    reach path 2 1 [false, false] [true, true] = false ∧
    reach path 2 2 [false, false] [true, true] = true ∧
    reach path 2 3 [true, true] [false, false] = false :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

example :
    Relation.RelatesWithinSteps
      (fun a b => a.length = 2 ∧ b.length = 2 ∧ path a b = true) [false, false] [true, true]
      (2 ^ 2) ∧
    ¬Relation.RelatesWithinSteps
      (fun a b => a.length = 2 ∧ b.length = 2 ∧ path a b = true) [false, false] [true, true]
      (2 ^ 1) :=
  ⟨(reach_iff (w := 2) (u := [false, false]) (v := [true, true]) rfl rfl).mp (by decide),
    by
      rw [← reach_iff (w := 2) (u := [false, false]) (v := [true, true]) rfl rfl]
      decide⟩

/-! ### An unreachable target -/

/-- Edges between the words with the same last bit: `{00, 10}` and `{01, 11}` are disconnected. -/
private def halves (u v : List Bool) : Bool := decide (u.getLast? = v.getLast?)

example :
    reach halves 2 1 [false, false] [true, false] = true ∧
    reach halves 2 3 [false, false] [true, true] = false ∧
    reach halves 2 1 [false, false] [true, true] = false ∧
    ¬Relation.RelatesWithinSteps
      (fun a b => a.length = 2 ∧ b.length = 2 ∧ halves a b = true) [false, false] [true, true]
      (2 ^ 3) :=
  ⟨by decide, by decide, by decide,
    by rw [← reach_iff (w := 2) (u := [false, false]) (v := [true, true]) rfl rfl]; decide⟩

/-! ### The trivial walk -/

example :
    reach (fun _ _ => false) 2 0 [true, false] [true, false] = true ∧
    reach (fun _ _ => false) 2 0 [true, false] [false, true] = false ∧
    reach (fun _ _ => false) 0 3 [] [] = true :=
  ⟨by decide, by decide, by decide⟩

/-! ### The certificate, for a family of depths -/

-- The midpoint recursion at depth `n`, with the width, the endpoints and the edge test fixed, in
-- polynomial space.
example : ComputableInPolySpace
    (fun n : ℕ => reach (fun u v => decide (u = v)) 1 n [false] [true]) encUnary encBool := by
  have hedge : ComputableInPolyTime
      (fun q : (List Bool × List Bool) × ℕ => decide (q.1.1 = q.1.2))
      (encPair (encPair encBits encBits) encUnary) encBool :=
    (ComputableInDegree.eqWords.comp
      (ComputableInDegree.fst (encPair encBits encBits) encUnary)).computableInPolyTime
  exact ComputableInPolySpace.reach (edge := fun _ u v => decide (u = v))
    (.of_polyTime (.const 1)) (.of_polyTime .id') (.of_polyTime (.const [false]))
    (.of_polyTime (.const [true])) (.of_polyTime hedge) fun _ => ⟨rfl, rfl⟩

end CslibFrontierTests.Savitch
