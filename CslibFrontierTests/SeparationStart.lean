/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Start
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! Tests of the start of the play on the blocks of a run, as a client that sees only the public
statements.

* `Cut.runVal_eq_sum_value_initial` for one block, one letter, one tape and no extra parties, with
  a code of one bit and units of one bit: its hypotheses on the code and on the numbers of units
  are discharged.
* `Cut.sum_value_initial` without blocks: there is one starting position, without units, and its
  value is `1`.
* `Cut.initialTable_ne_none` for the first and for the second holder of an initial unit, and
  `Cut.initialTable_congr` for contents that differ in the new units only. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationStart

open Finset Cslib Cslib.Circuits.Arithmetic.Separation Cslib.Circuits.Arithmetic.Separation.Tape
open Cslib.Circuits.Arithmetic.Separation.Cut

variable {F Q : Type} [Fintype Q] [DecidableEq Q]

/-- A code of one bit for one letter and the separator. -/
private def code : Option Unit → BitString 1 := fun o _ => o.isSome

private theorem code_injective : Function.Injective code := fun o o' h => by
  have := congrFun h 0
  cases o <;> cases o' <;> simp_all [code]

/-- One block of `T` steps on one tape, over one letter: the value of the automaton is a sum of
values of starting positions on two parties, the block and the input. A string between two
parties has at most `T + 3` units of one bit. -/
example [CommRing F] (mu : Letter Unit Unit Unit → Matrix Q Q F) (i e : Q) (T : ℕ)
    (u : Unit → List Unit) (hu : (u ()).length ≤ T) :
    runVal mu i e (1 * T) u = ∑ q : Fin (1 + 1) → Q, if q 0 = i ∧ q (Fin.last 1) = e then
      ∑ ρ : Option Unit → Fin (1 + 1) → RowData (1 + 1), if ValidRows ρ then
        ∑ n : Fin (1 + 1) → Fin (1 + 1) → Fin (T + 3 + 1),
          Play.value (UnitId.holder (Empty.elim : Empty → Bool → Fin (1 + 1 + 0)))
            (none : UnitContent 1) (initialUnits (U1 := 0) n) (initialUnits n) fun y =>
              ∏ p : Fin (1 + 1), initialTable mu T code q (parts T (u ())) (fun s => ρ s p)
                (fun a b => n a b) p (y (Fin.castAdd 0 p))
        else 0
      else 0 :=
  runVal_eq_sum_value_initial code_injective one_pos one_pos (by simp) _ i e u le_rfl
    (by simpa using hu)

/-- Without blocks there are no parties and no units, and the only starting position has the
value `1`. -/
example [CommSemiring F] (mu : Letter Unit Unit Unit → Matrix Q Q F) (q : Fin 1 → Q)
    (n : Fin (0 + 0) → Fin (0 + 0) → Fin (3 + 1)) :
    Play.value (UnitId.holder (Empty.elim : Empty → Bool → Fin (0 + 0 + 0)))
      (none : UnitContent 1) (initialUnits (U1 := 0) n) (initialUnits n) (fun _ => (1 : F)) =
        1 := by
  have : IsEmpty (Fin (0 + 0)) := Fin.isEmpty
  have h := sum_value_initial (mu := mu) (T := 0) (U0 := 3) (U1 := 0) (A' := 0) (x := Fin.elim0)
    code_injective one_pos one_pos (by simp) (Empty.elim : Empty → Bool → Fin (0 + 0 + 0)) q
    fun κ => κ.elim0
  have hseg : segments Unit Unit 0 0 = univ :=
    eq_univ_of_forall fun X => mem_segments.2 fun _ a => isEmptyElim a
  have hρ (ρ : Option Unit → Fin (0 + 0) → RowData (0 + 0)) : ValidRows ρ :=
    fun _ p => isEmptyElim p
  simp only [Fintype.sum_subsingleton _ n] at h
  simpa [hseg, hρ, segmentWeight, List.StairRefinement.Stair] using h

section Tables

variable [CommSemiring F] {N : Type} [Fintype N] {K T U0 U1 A' c ub : ℕ}
  {mu : Letter Unit Unit Unit → Matrix Q Q F} {cb : Option Unit → BitString c}
  {q : Fin (K + 1) → Q} {x : Fin K → List Unit} {ρ : Option Unit → RowData (K + K)}
  {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {p b : Fin (K + K)}
  {y : UnitId (K + K) U0 N U1 → UnitContent ub}

/-- A base party whose table is not zero has its copies of the units of the strings that it
writes: it is the first holder of these units. -/
example (np : N → Bool → Fin (K + K + A'))
    (h : initialTable mu T cb q x ρ (fun a b => n a b) p y ≠ 0) (k : Fin U0)
    (hk : (k : ℕ) < n p b) : y (.init p b k) ≠ none :=
  initialTable_ne_none h _ (init_mem_initialUnits.2 hk)
    (Play.holds_end (UnitId.holder np) (.init p b k) false)

/-- Likewise for the strings that it reads: it is the second holder of their units. So its table
vanishes if a unit of such a string is absent. -/
example (np : N → Bool → Fin (K + K + A')) (k : Fin U0) (hk : (k : ℕ) < n b p)
    (hy : y (.init b p k) = none) : initialTable mu T cb q x ρ (fun a b => n a b) p y = 0 :=
  by_contra fun h => initialTable_ne_none h _ (init_mem_initialUnits.2 hk)
    (Play.holds_end (UnitId.holder np) (.init b p k) true) hy

/-- The table at the beginning does not read the new units. -/
example (m : Fin (K + K) → Fin (K + K) → ℕ) (z : N → Fin U1 → UnitContent ub) :
    initialTable mu T cb q x ρ m p y = initialTable mu T cb q x ρ m p fun
      | .init a b k => y (.init a b k)
      | .new ν k => z ν k :=
  initialTable_congr fun _ _ _ => rfl

end Tables

end CslibFrontierTests.SeparationStart
