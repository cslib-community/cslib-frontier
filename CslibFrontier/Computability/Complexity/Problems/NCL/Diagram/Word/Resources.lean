/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word
import Mathlib.Data.List.GetD

/-!
# Resource bounds for word execution

Each layer has a fixed allowance for new wire positions and edge names. Summing these
allowances bounds every run's wire stack and edge counter. Existing vertex output is carried
through as an unchanged prefix.

## Main definitions

* `Cslib.Complexity.NCL.Slice.shift`: shift a layer's wire offset.
* `Cslib.Complexity.NCL.Word.cost`: a word's total local resource allowance.

## Main results

* `Cslib.Complexity.NCL.Word.run_resources`: bounds on edge names and wire-stack length.
* `Cslib.Complexity.NCL.Word.run_verts_append`: vertex output preserves an existing prefix.
* `Cslib.Complexity.NCL.Diagram.toWord_shift`: diagram shifts agree with layer shifts.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL

/-- Shift a layer's wire offset. -/
@[expose] def Slice.shift (k : ℕ) : Slice → Slice
  | .gen j a b vs => .gen (k + j) a b vs
  | .swap j => .swap (k + j)

/-- A bound on the new wire positions and edge numbers created by one layer. -/
@[expose] def Slice.cost : Slice → ℕ
  | .gen _ _ b _ => b.length
  | .swap _ => 2

/-- Sum the local wire bounds of a word. -/
@[expose] def Word.cost (w : Word) : ℕ := (w.map Slice.cost).sum

private theorem Slice.run_next_le (s : Slice) (st : Word.State) :
    (s.run st).next ≤ st.next + s.cost := by cases s <;> simp [run, cost]

private theorem Slice.run_length_wires_le (s : Slice) (st : Word.State) :
    (s.run st).wires.length ≤ st.wires.length + s.cost := by
  cases s <;>
    simp only [run, cost, List.length_append, List.length_take, List.length_ofFn, List.length_cons,
      List.length_nil, List.length_drop] <;> omega

private theorem Slice.run_wires_le (s : Slice) (st : Word.State)
    (h : ∀ e ∈ st.wires, e ≤ st.next) : ∀ e ∈ (s.run st).wires, e ≤ (s.run st).next := by
  have hg (i : ℕ) : st.wires.getD i 0 ≤ st.next := by
    by_cases hi : i < st.wires.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · simp [Nat.le_of_not_gt hi]
  cases s with
  | gen k a b vs =>
    simp only [run, List.mem_append, List.mem_ofFn]
    rintro e ((he | ⟨i, rfl⟩) | he)
    · exact (h e ((List.take_sublist k _).subset he)).trans (Nat.le_add_right ..)
    · omega
    · exact (h e ((List.drop_sublist (k + a.length) _).subset he)).trans (Nat.le_add_right ..)
  | swap k =>
    simp only [run, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro e ((he | rfl | rfl) | he)
    exacts [h e ((List.take_sublist k _).subset he), hg _, hg _,
      h e ((List.drop_sublist (k + 2) _).subset he)]

/-- Running a word preserves bounded wire labels and adds at most its cost to both counters. -/
theorem Word.run_resources (w : Word) (st : Word.State)
    (h : ∀ e ∈ st.wires, e ≤ st.next) :
    (w.run st).next ≤ st.next + w.cost ∧
    (w.run st).wires.length ≤ st.wires.length + w.cost ∧
    ∀ e ∈ (w.run st).wires, e ≤ (w.run st).next := by
  induction w generalizing st with
  | nil => simpa [run, cost] using h
  | cons s w ih =>
    have hn := s.run_next_le st
    have hl := s.run_length_wires_le st
    obtain ⟨hn', hl', hb⟩ := ih (s.run st) (s.run_wires_le st h)
    simp only [run, List.foldl_cons, cost, List.map_cons, List.sum_cons] at *
    exact ⟨by omega, by omega, hb⟩

/-- A preexisting vertex list remains a prefix and does not affect the new vertices. -/
theorem Word.run_verts_append (w : Word) (st : Word.State) (vs : List (Vertex ℕ)) :
    w.run ⟨st.wires, st.next, vs ++ st.verts⟩ =
      let out := w.run st
      ⟨out.wires, out.next, vs ++ out.verts⟩ := by
  induction w generalizing st with
  | nil => rfl
  | cons s w ih =>
    have hs : s.run ⟨st.wires, st.next, vs ++ st.verts⟩ =
        ⟨(s.run st).wires, (s.run st).next, vs ++ (s.run st).verts⟩ := by
      cases s <;> simp [Slice.run, List.append_assoc]
    simpa only [Word.run, List.foldl_cons, hs] using ih (s.run st)

namespace Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ)

/-- Shifting a diagram shifts every layer of its emitted word by the same offset. -/
theorem toWord_shift {a b : List Color} (D : Diagram Γ a b) (k j : ℕ) :
    D.toWord I (k + j) = (D.toWord I j).map (Slice.shift k) := by
  induction D generalizing k j with
  | gen g => rfl
  | id a => rfl
  | swap x y => rfl
  | comp D₁ D₂ ih₁ ih₂ => simp only [toWord, List.map_append, ih₁, ih₂]
  | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [toWord, List.map_append, ih₁]
    rw [Nat.add_assoc, ih₂]

end Diagram
end Cslib.Complexity.NCL
