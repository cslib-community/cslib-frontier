/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridLayout

/-!
# Complete paths through one grid layer

Join both routing bands to the middle cell paths. Each bypass has one path from top to bottom;
each cell input ends at the vertex and each cell output starts there.

## Main definitions

* `Cslib.Complexity.NCL.GridLayout.Layer.Trace`: complete strand traces.

## Main results

* `Cslib.Complexity.NCL.GridLayout.Layer.connected`: every strand is a finite orthogonal path.
* `Cslib.Complexity.NCL.GridLayout.Layer.meet`: only cell incidences can intersect.
-/

public section

namespace Cslib.Complexity.NCL.GridLayout

open GridRouting GridDrawing

variable {k a b r : ℕ}

/-- The top interface port used by a strand, if any. -/
@[expose] def inputIndex : Strand k a b r → Option (Fin (k + a + r))
  | .inl i => some ⟨i, by have := i.isLt; omega⟩
  | .inr (.inl (.inl i)) => some ⟨k + i, by have := i.isLt; omega⟩
  | .inr (.inl (.inr _)) => none
  | .inr (.inr j) => some ⟨k + a + j, by have := j.isLt; omega⟩

/-- The bottom interface port used by a strand, if any. -/
@[expose] def outputIndex : Strand k a b r → Option (Fin (k + b + r))
  | .inl i => some ⟨i, by have := i.isLt; omega⟩
  | .inr (.inl (.inl _)) => none
  | .inr (.inl (.inr j)) => some ⟨k + j, by have := j.isLt; omega⟩
  | .inr (.inr j) => some ⟨k + b + j, by have := j.isLt; omega⟩

/-- The strand reached by an ordered top interface port. -/
@[expose] def inputStrand (i : Fin (k + a + r)) : Strand k a b r :=
  if h : i.val < k then .inl ⟨i, h⟩
  else if h' : i.val < k + a then .inr (.inl (.inl ⟨i.val - k, by omega⟩))
  else .inr (.inr ⟨i.val - (k + a), by have := i.isLt; omega⟩)

/-- The strand reached by an ordered bottom interface port. -/
@[expose] def outputStrand (j : Fin (k + b + r)) : Strand k a b r :=
  if h : j.val < k then .inl ⟨j, h⟩
  else if h' : j.val < k + b then .inr (.inl (.inr ⟨j.val - k, by omega⟩))
  else .inr (.inr ⟨j.val - (k + b), by have := j.isLt; omega⟩)

@[simp] theorem inputIndex_inputStrand (i : Fin (k + a + r)) :
    inputIndex (inputStrand (b := b) i) = some i := by
  unfold inputStrand
  split_ifs <;> simp only [inputIndex, Option.some.injEq, Fin.ext_iff] <;> omega

@[simp] theorem outputIndex_outputStrand (j : Fin (k + b + r)) :
    outputIndex (outputStrand (a := a) j) = some j := by
  unfold outputStrand
  split_ifs <;> simp only [outputIndex, Option.some.injEq, Fin.ext_iff] <;> omega

/-- A strand with an input port is uniquely determined by that port. -/
theorem inputStrand_of_index (e : Strand k a b r) (i : Fin (k + a + r))
    (hi : inputIndex e = some i) : inputStrand i = e := by
  rcases e with j | ((j | j) | j) <;> simp only [inputIndex, Option.some.injEq] at hi
  · subst i
    simp [inputStrand, j.isLt]
  · subst i
    simp [inputStrand, show ¬k + j.val < k by omega,
      show k + j.val < k + a by have := j.isLt; omega]
  · cases hi
  · subst i
    simp [inputStrand, show ¬k + a + j.val < k by omega,
      show ¬k + a + j.val < k + a by omega]

/-- A strand with an output port is uniquely determined by that port. -/
theorem outputStrand_of_index (e : Strand k a b r) (j : Fin (k + b + r))
    (hj : outputIndex e = some j) : outputStrand j = e := by
  rcases e with i | ((i | i) | i) <;> simp only [outputIndex, Option.some.injEq] at hj
  · subst j
    simp [outputStrand, i.isLt]
  · cases hj
  · subst j
    simp [outputStrand, show ¬k + i.val < k by omega,
      show k + i.val < k + b by have := i.isLt; omega]
  · subst j
    simp [outputStrand, show ¬k + b + i.val < k by omega,
      show ¬k + b + i.val < k + b by omega]

/-- The unique cell vertex in the layer's own coordinates. -/
@[expose] def Layer.center (_L : Layer k a b r) : Point :=
  (4 * k + GridStar.center a, 2 * (k + a + r + 1) + 1)

/-- A strand starts on the top row when it has an input port, and at the cell otherwise. -/
@[expose] def Layer.source (L : Layer k a b r) (e : Strand k a b r) : Point :=
  (inputIndex e).elim L.center fun i => (4 * i.val, 0)

/-- A strand ends on the bottom row when it has an output port, and at the cell otherwise. -/
@[expose] def Layer.target (L : Layer k a b r) (e : Strand k a b r) : Point :=
  (outputIndex e).elim L.center fun j => (4 * j.val, L.height)

/-- The upper, middle and lower pieces of the strand in their consecutive row bands. -/
@[expose] def Layer.Trace (L : Layer k a b r) (e : Strand k a b r) (p : Point) : Prop :=
  (∃ i, inputIndex e = some i ∧ L.upper.Contains i p) ∨
    Shift (2 * (k + a + r + 1)) (MiddleContains e) p ∨
      (2 * (k + a + r + 1) + 2 ≤ p.2 ∧ ∃ j, outputIndex e = some j ∧
        L.lower.Contains j (p.1, p.2 - (2 * (k + a + r + 1) + 2)))

/-- A strand incident to the cell, rather than a bypass. -/
@[expose] def IsCell (e : Strand k a b r) : Prop := ∃ q, e = .inr (.inl q)

/-- The cell vertex is strictly inside its drawing band. -/
theorem Layer.center_rows (L : Layer k a b r) :
    0 < L.center.2 ∧ L.center.2 < L.height := by
  simp only [center, height]
  omega

/-- Every complete strand has positive downward endpoint displacement. -/
theorem Layer.edge_rows (L : Layer k a b r) (e : Strand k a b r) :
    (L.source e).2 < (L.target e).2 := by
  rcases e with i | ((i | j) | j)
  · exact L.height_pos
  · exact L.center_rows.1
  · exact L.center_rows.2
  · exact L.height_pos

/-- Each upper band supplies its actual orthogonal path. -/
private theorem Layer.connected_upper (L : Layer k a b r) (e : Strand k a b r)
    (i : Fin (k + a + r)) (hi : inputIndex e = some i) :
    Connected (L.Trace e) (4 * i.val, 0) (columns k a r i, 2 * (k + a + r + 1)) :=
  ⟨L.upper.path i, fun p hp => .inl ⟨i, hi, (L.upper.path_contains_iff i p).1 hp⟩⟩

/-- Translate the cell-band path into its full-layer position. -/
private theorem Layer.connected_middle (L : Layer k a b r) (e : Strand k a b r) :
    Connected (L.Trace e)
      (shift (2 * (k + a + r + 1)) (middleStart e))
      (shift (2 * (k + a + r + 1)) (middleEnd e)) := by
  have hm : Connected (MiddleContains e) (middleStart e) (middleEnd e) :=
    ⟨middlePath e, fun p hp => (middlePath_contains_iff e p).1 hp⟩
  exact (hm.shift _).mono fun _ hp => .inr (.inl hp)

/-- Translate the lower routing into its full-layer position. -/
private theorem Layer.connected_lower (L : Layer k a b r) (e : Strand k a b r)
    (j : Fin (k + b + r)) (hj : outputIndex e = some j) :
    Connected (L.Trace e) (columns k b r j, 2 * (k + a + r + 1) + 2)
      (4 * j.val, L.height) := by
  have hm : Connected (L.lower.Contains j) (columns k b r j, 0)
      (4 * j.val, 2 * (k + b + r + 1)) :=
    ⟨L.lower.path j, fun p hp => (L.lower.path_contains_iff j p).1 hp⟩
  have ht := (hm.shift (2 * (k + a + r + 1) + 2)).mono
    (fun _ hp => Or.inr (Or.inr ⟨hp.1, j, hj, hp.2⟩) :
      ∀ p, Shift (2 * (k + a + r + 1) + 2) (L.lower.Contains j) p → L.Trace e p)
  change Connected (L.Trace e) _ _ at ht
  convert ht using 1 <;> apply Prod.ext <;> simp only [GridDrawing.shift, Layer.height] <;> omega

private theorem middleStart_index (e : Strand k a b r) :
    middleStart e = (inputIndex e).elim (4 * k + GridStar.center a, 1)
      (fun i => (columns k a r i, 0)) := by
  rcases e with i | ((i | j) | j) <;>
    simp only [middleStart, inputIndex, Option.elim_some, Option.elim_none,
      columns_prefix, columns_cell, columns_suffix] <;> congr 1 <;> omega

private theorem middleEnd_index (e : Strand k a b r) :
    middleEnd e = (outputIndex e).elim (4 * k + GridStar.center a, 1)
      (fun j => (columns k b r j, 2)) := by
  rcases e with i | ((i | j) | j) <;>
    simp only [middleEnd, outputIndex, Option.elim_some, Option.elim_none,
      columns_prefix, columns_cell, columns_suffix] <;> congr 1 <;> omega

/-- Each complete strand has a finite orthogonal path joining its declared endpoints. -/
theorem Layer.connected (L : Layer k a b r) (e : Strand k a b r) :
    Connected (L.Trace e) (L.source e) (L.target e) := by
  have hm := L.connected_middle e
  rw [middleStart_index] at hm
  have hu : Connected (L.Trace e) (L.source e) (shift (2 * (k + a + r + 1)) (middleEnd e)) := by
    cases hi : inputIndex e with
    | none => simpa [source, hi, center, shift, Nat.add_comm] using hm
    | some i =>
      rw [hi] at hm
      simpa [source, hi] using (L.connected_upper e i hi).comp (by simpa [shift] using hm)
  rw [middleEnd_index] at hu
  cases hj : outputIndex e with
  | none => simpa [target, hj, center, shift, Nat.add_comm] using hu
  | some j =>
    rw [hj] at hu
    simpa [target, hj] using Connected.comp
      (by simpa [shift, Nat.add_comm] using hu) (L.connected_lower e j hj)

/-- An input strand starts at its standard top port. -/
theorem Layer.source_of_input (L : Layer k a b r) (e : Strand k a b r)
    (i : Fin (k + a + r)) (hi : inputIndex e = some i) : L.source e = (4 * i.val, 0) := by
  simp [source, hi]

/-- An output strand ends at its standard bottom port. -/
theorem Layer.target_of_output (L : Layer k a b r) (e : Strand k a b r)
    (j : Fin (k + b + r)) (hj : outputIndex e = some j) : L.target e = (4 * j.val, L.height) := by
  simp [target, hj]

private theorem middle_top_of_input (e : Strand k a b r) (i : Fin (k + a + r))
    (hi : inputIndex e = some i) : MiddleContains e (columns k a r i, 0) := by
  simpa only [middleStart_index, hi, Option.elim_some] using
    (middlePath_contains_iff e _).1 (middlePath e).source_mem

private theorem middle_bottom_of_output (e : Strand k a b r) (j : Fin (k + b + r))
    (hj : outputIndex e = some j) : MiddleContains e (columns k b r j, 2) := by
  simpa only [middleEnd_index, hj, Option.elim_some] using
    (middlePath_contains_iff e _).1 (middlePath e).target_mem

/-- All complete strand traces stay inside the layer band. -/
theorem Layer.row_le (L : Layer k a b r) (e : Strand k a b r) (p : Point)
    (hp : L.Trace e p) : p.2 ≤ L.height := by
  simp only [height]
  rcases hp with ⟨i, _, hp⟩ | ⟨_, hp⟩ | ⟨_, j, _, hp⟩
  · have := L.upper.row_le i hp
    omega
  · have := middle_row_le L.arity hp
    omega
  · have := L.lower.row_le j hp
    omega

/-- The first row consists precisely of the declared input strand endpoints. -/
theorem Layer.top_iff (L : Layer k a b r) (e : Strand k a b r) (x : ℕ) :
    L.Trace e (x, 0) ↔ ∃ i, inputIndex e = some i ∧ x = 4 * i.val := by
  simp only [Trace, Shift, OrderedRouting.top_iff]
  exact ⟨by rintro (h | ⟨hy, _⟩ | ⟨hy, _⟩) <;> first | exact h | omega, .inl⟩

/-- The last row consists precisely of the declared output strand endpoints. -/
theorem Layer.bottom_iff (L : Layer k a b r) (e : Strand k a b r) (x : ℕ) :
    L.Trace e (x, L.height) ↔ ∃ j, outputIndex e = some j ∧ x = 4 * j.val := by
  have hr : L.height - (2 * (k + a + r + 1) + 2) = 2 * (k + b + r + 1) := by
    simp only [height]; omega
  refine ⟨?_, fun ⟨j, hj, hx⟩ => .inr (.inr ⟨by simp only [height]; omega, j, hj,
    hr.symm ▸ (L.lower.bottom_iff j x).2 hx⟩)⟩
  rintro (⟨i, _, hu⟩ | ⟨_, hm⟩ | ⟨_, j, hj, hl⟩)
  · have := L.upper.row_le i hu
    simp only [height] at this; omega
  · have := middle_row_le L.arity hm
    simp only [height] at this; omega
  · exact ⟨j, hj, (L.lower.bottom_iff j x).1 (hr ▸ hl)⟩

private theorem upper_middle_same (L : Layer k a b r) {e f : Strand k a b r}
    {i : Fin (k + a + r)} {p : Point} (hi : inputIndex e = some i)
    (hu : L.upper.Contains i p) (hm : Shift (2 * (k + a + r + 1)) (MiddleContains f) p) :
    e = f := by
  obtain ⟨heq, hx⟩ := L.upper_middle_intersection i f p hu hm
  exact middle_boundary_unique L.arity (.inl rfl) (middle_top_of_input e i hi)
    (by simpa only [heq, hx, Nat.sub_self] using hm.2)

private theorem lower_middle_same (L : Layer k a b r) {e f : Strand k a b r}
    {j : Fin (k + b + r)} {p : Point} (hj : outputIndex e = some j)
    (hl : Shift (2 * (k + a + r + 1) + 2) (L.lower.Contains j) p)
    (hm : Shift (2 * (k + a + r + 1)) (MiddleContains f) p) : e = f := by
  have hlocal : 2 ≤ p.2 - 2 * (k + a + r + 1) ∧
      L.lower.Contains j (p.1, p.2 - 2 * (k + a + r + 1) - 2) :=
    ⟨by have := hl.1; omega,
      by simpa only [Nat.sub_sub] using hl.2⟩
  obtain ⟨_, hx⟩ := L.middle_lower_intersection f j p.1 (p.2 - 2 * (k + a + r + 1)) hm.2 hlocal
  have heq : p.2 = 2 * (k + a + r + 1) + 2 := by have := hm.1; omega
  exact middle_boundary_unique L.arity (.inr rfl) (middle_bottom_of_output e j hj)
    (by simpa only [heq, hx, Nat.add_sub_cancel_left] using hm.2)

/-- Distinct full strands intersect only at their common cell vertex. -/
theorem Layer.meet (L : Layer k a b r) {e f : Strand k a b r} (hef : e ≠ f)
    (p : Point) (he : L.Trace e p) (hf : L.Trace f p) :
    p = L.center ∧ IsCell e ∧ IsCell f := by
  rcases he with ⟨i, hi, hu⟩ | hm | ⟨hy, j, hj, hl⟩ <;>
    rcases hf with ⟨i', hi', hu'⟩ | hm' | ⟨hy', j', hj', hl'⟩
  · rcases eq_or_ne i i' with rfl | hii
    · exact (hef ((inputStrand_of_index e i hi).symm.trans (inputStrand_of_index f i hi'))).elim
    · exact (L.upper.disjoint hii p ⟨hu, hu'⟩).elim
  · exact (hef (upper_middle_same L hi hu hm')).elim
  · exact (L.upper_lower_disjoint i p hu hy').elim
  · exact (hef (upper_middle_same L hi' hu' hm).symm).elim
  · obtain ⟨hp, he, hf⟩ := middle_intersection L.arity hef hm.2 hm'.2
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    have := hm.1
    exact ⟨Prod.ext hx (by simp only [center] at hy ⊢; omega), he, hf⟩
  · exact (hef (lower_middle_same L hj' ⟨hy', hl'⟩ hm).symm).elim
  · exact (L.upper_lower_disjoint i' p hu' hy).elim
  · exact (hef (lower_middle_same L hj ⟨hy, hl⟩ hm')).elim
  · rcases eq_or_ne j j' with rfl | hjj
    · exact (hef ((outputStrand_of_index e j hj).symm.trans (outputStrand_of_index f j hj'))).elim
    · exact (L.lower.disjoint hjj _ ⟨hl, hl'⟩).elim

/-- Only cell-incidence strands can pass through the cell vertex. -/
theorem Layer.vertex_meet (L : Layer k a b r) (e : Strand k a b r)
    (he : L.Trace e L.center) : IsCell e := by
  have hc : GridStar.center a ≤ 1 := by unfold GridStar.center; split <;> omega
  rcases he with ⟨i, _, hu⟩ | hm | ⟨hy, _⟩
  · have := L.upper.row_le i hu
    simp only [center] at this; omega
  · rcases e with i | (e | j)
    · have hi := i.isLt
      have : L.center.1 = 4 * i.val := hm.2.1
      simp only [center] at this; omega
    · exact ⟨e, rfl⟩
    · have : L.center.1 = 4 * k + 4 + 4 * j.val := hm.2.1
      simp only [center] at this; omega
  · simp only [center] at hy; omega

end Cslib.Complexity.NCL.GridLayout
