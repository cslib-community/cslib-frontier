/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Rows
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Segments
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.ReduceOption

/-! Tests of the blocks of a run, the segments between its parties and row data, as a client that
sees only the public statements.

* Row data on small matrices of words: a staircase, a matrix without staircase support, and an
  empty row, whose row data repeat the last column of the row before.
* The value of a run of `K * T` steps as a sum over states and over segments with staircase
  support, from `Cut.runVal_blocks` and `Cut.sum_segments` with the parts of the input, and
  blocks without steps.
* The parts of a word, what a block emits, and the bit string of segments. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationBlocks

open Finset List.StairRefinement Cslib.Circuits.Arithmetic.Separation
open Cslib.Circuits.Arithmetic.Separation.Tape Cslib.Circuits.Arithmetic.Separation.Cut

/-! ### Row data -/

/-- A staircase: the first row uses both columns and the second row the last one. -/
private def stairX : Fin 2 → Fin 2 → List Bool := ![![[true], [false]], ![[], [true]]]

/-- Its row data. -/
private def stairRows : Fin 2 → RowData 2 := ![⟨false, 0, 1⟩, ⟨false, 1, 1⟩]

/-- The row data are valid and fit the rows, so the matrix has staircase support and they are
its row data. -/
example : Stair stairX ∧ stairRows = rowsOf stairX := validRow_and_ok_iff.1 (by decide)

/-- Row data that begin the second row before the end of the first one are not valid. -/
example : ¬ValidRow ![⟨false, 0, 1⟩, ⟨false, 0, 1⟩] (1 : Fin 2) := by decide

/-- The second row uses a column before the one that the first row uses: no staircase support,
hence no valid row data that fit the rows. -/
example (ρ : Fin 2 → RowData 2) :
    ¬((∀ p, ValidRow ρ p) ∧ ∀ p, (ρ p).Ok ((![![[], [true]], ![[true], []]] :
      Fin 2 → Fin 2 → List Bool) p)) :=
  fun h => absurd (validRow_and_ok_iff.1 h).1 (by decide)

/-- An empty second row: its row data repeat the last column of the first row. -/
private def emptyRowX : Fin 2 → Fin 2 → List Bool := ![![[], [true]], ![[], []]]

example : rowsOf emptyRowX = ![⟨false, 1, 1⟩, ⟨true, 1, 1⟩] :=
  (validRow_and_ok_iff.1 (by decide)).2.symm

/-- Row data of the empty row that do not repeat that column fit the row but are not valid. -/
example : (⟨true, 0, 0⟩ : RowData 2).Ok (emptyRowX 1) ∧
    ¬ValidRow ![⟨false, 1, 1⟩, ⟨true, 0, 0⟩] (1 : Fin 2) := by decide

/-- All row data on the tapes `Bool` are checked together. -/
example : ValidRows fun _ : Bool => stairRows := by decide

/-- Row data form a finite type, so one can sum over them: for one party there are two valid
ones, of an empty and of a non-empty row. -/
example : Fintype.card (RowData 2) = 8 := by decide
example : (univ.filter fun ρ : Unit → Fin 1 → RowData 1 => ValidRows ρ).card = 2 := by decide

/-! ### Blocks and segments -/

section Run

variable {F Γ S Q : Type} [CommRing F] [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

/-- The value of an automaton with one input on a run of `K * T` steps, for an input of at most
`K * ℓ` letters with `ℓ ≤ T`: a sum over the states between the blocks and over the segments with
staircase support, where the input parties hold the parts of the input. -/
example (mu : Letter S Unit Γ → Matrix Q Q F) (i e : Q) (K T ℓ : ℕ) (hℓ : ℓ ≤ T)
    (u : Unit → List Γ) (hu : (u ()).length ≤ K * ℓ) :
    runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ X ∈ segments Γ S K T,
        if ∀ s, Stair (X s) then segmentWeight mu T q (parts ℓ (u ())) X else 0
      else 0 := by
  rw [runVal_blocks]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_segments q (fun κ => (length_parts_le ℓ (u ()) κ).trans hℓ) u
    (by rw [cat_parts, List.take_of_length_le hu])]

/-- One block: the value on a run of `T` steps is the sum, over the words that the run emits,
with the same word on the two sides of every tape and the input on the input channel, of the
weights of the block from `i` to `e`. -/
example (mu : Letter S Unit Γ → Matrix Q Q F) (i e : Q) (T : ℕ) (u : Unit → List Γ) :
    runVal mu i e (1 * T) u =
      ∑ v ∈ Fintype.piFinset fun _ : Ch S Unit => List.wordsLe Γ T,
        if (∀ s, v (.tp s false) = v (.tp s true)) ∧ ∀ j, v (.inp j) = u j then
          blockWeight mu T i e v else 0 := by
  rw [runVal_blocks, sum_eq_single ![i, e]]
  · rw [ite_eq_left ⟨rfl, rfl⟩]
    refine sum_nbij' (fun v => v 0) (fun w _ => w) (fun v hv => Fintype.mem_piFinset.1 hv 0)
      (fun w hw => Fintype.mem_piFinset.2 fun _ => hw)
      (fun v _ => funext fun k => by rw [Subsingleton.elim k 0]) (fun _ _ => rfl) fun v _ => ?_
    simp [cat]
  · exact fun q _ hq => ite_eq_right fun h => hq (funext (Fin.forall_fin_two.2 ⟨h.1, h.2⟩))
  · simp

/-- A block without steps does not change the state and emits nothing. -/
example (mu : Letter S Unit Γ → Matrix Q Q F) (q : Q) :
    blockWeight mu 0 q q (fun _ => []) = 1 := by
  simp [blockWeight, emit]

example (mu : Letter S Unit Γ → Matrix Q Q F) (q q' : Q) (v : Ch S Unit → List Γ)
    (h : blockWeight mu 0 q q' v ≠ 0) (z : Ch S Unit) : v z = [] := by
  simpa using blockWeight_ne_zero h z

/-- An input party that writes its part of the input, on the input tape only, has weight `1`. -/
example (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (q : Fin 2 → Q) (w : List Γ) :
    partyWeight mu T q (fun _ => w) (Fin.natAdd 1 0)
      (fun s b => if s = none ∧ b = 0 then w else []) (fun _ _ => []) = 1 := by
  rw [partyWeight_input, ite_eq_left]
  exact ⟨by simp, by simp, by simp [cat]⟩

end Run

/-- The parts of a word of five letters, of two letters each: the fifth letter is in no part. -/
example : (parts 2 [1, 2, 3, 4, 5] : Fin 2 → List ℕ) = ![[1, 2], [3, 4]] := by decide

example : cat (parts 2 [1, 2, 3, 4, 5] : Fin 2 → List ℕ) ≠ [1, 2, 3, 4, 5] := by
  rw [cat_parts]
  decide

/-- What a block emits on a tape `()`: what it writes for the two parties on one side, what it
reads from them on the other side, and what it reads from the input tape `none`. -/
private def writes : Option Unit → Fin 2 → List Bool
  | none, _ => []
  | some _, b => [b = 0]

private def reads : Option Unit → Fin 2 → List Bool
  | none, b => [b = 1, true]
  | some _, _ => [false]

example : blockEmission writes reads (.tp () false) = [true, false] := by decide
example : blockEmission writes reads (.tp () true) = [false, false] := by decide
example : blockEmission writes reads (.inp ()) = [false, true, true, true] := by decide

/-- A code of the letters `Bool` and of the separator by two bits. -/
private def code : Option Bool → Cslib.BitString 2
  | none => ![true, true]
  | some b => ![false, b]

/-- One letter on each of two tapes: two letters and two separators, of two bits each. -/
example : (segmentString code fun _ : Bool => [true]).length = 8 := by
  simp [length_segmentString]

/-- Segments that differ on one tape have different bit strings. -/
example : segmentString code (fun s : Bool => [s]) ≠ segmentString code fun _ : Bool => [true] :=
  (segmentString_injective (by decide) Nat.zero_lt_two).ne
    fun h => absurd (congrFun h false) (by decide)

/-- Three parties and empty segments on two tapes: every bit string consists of the two
separators, which fill one unit of four bits, so it has two units. -/
example (X : Bool → Fin 3 → List Bool) (h : ∀ s b, X s b = []) :
    ∑ b, unitCount 4 (segmentString code fun s => X s b) ≤ 6 := by
  have := sum_unitCount_le (T := 0) (ub := 4) (cb := code) (X := X) (by simp [cat_eq_nil.2 (h _)])
  simpa using this

end CslibFrontierTests.SeparationBlocks
