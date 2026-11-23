/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridPath
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridStar

/-!
# Grid layout of one plane layer

Expand the ports of a cell into a three-column window. The bypass wires stay outside that
window. Two ordered routing bands connect these ports to the standard columns `4 * i` at the
top and bottom, so successive layers have identical interfaces.

## Main definitions

* `Cslib.Complexity.NCL.GridLayout.columns`: the ordered columns around a cell.
* `Cslib.Complexity.NCL.GridLayout.Layer`: routing bands around a three-port cell.

## Main results

* `Cslib.Complexity.NCL.GridLayout.middle_intersection`: only cell ports meet at the vertex.
* `Cslib.Complexity.NCL.GridLayout.layer`: construct the routing bands for every plane layer.
-/

public section

namespace Cslib.Complexity.NCL.GridLayout

open GridRouting

/-- Ordered port columns: prefix wires, the cell's ports, and suffix wires. -/
@[expose] def columns (k a r : ℕ) (i : Fin (k + a + r)) : ℕ :=
  if i.val < k then 4 * i.val
  else if i.val < k + a then 4 * k + (i.val - k)
  else 4 * k + 4 + 4 * (i.val - (k + a))

/-- The cell occupies at most three columns, leaving a gap before the suffix wires. -/
theorem columns_strictMono (k a r : ℕ) (ha : a ≤ 3) : StrictMono (columns k a r) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  simp only [columns]
  split_ifs <;> omega

/-- The columns of the first `k` bypass wires. -/
theorem columns_prefix (k a r : ℕ) (i : Fin k) :
    columns k a r ⟨i, by omega⟩ = 4 * i := by
  simp [columns, i.isLt]

/-- The columns occupied by the cell ports. -/
theorem columns_cell (k a r : ℕ) (i : Fin a) :
    columns k a r ⟨k + i, by omega⟩ = 4 * k + i := by
  simp [columns, show ¬k + i.val < k by omega, show k + i.val < k + a by omega]

/-- The columns of the suffix bypass wires. -/
theorem columns_suffix (k a r : ℕ) (i : Fin r) :
    columns k a r ⟨k + a + i, by omega⟩ = 4 * k + 4 + 4 * i := by
  simp [columns, show ¬k + a + i.val < k by omega,
    show ¬k + a + i.val < k + a by omega]

/-- The strands in the middle band: prefix, cell ports, and suffix. -/
abbrev Strand (k a b r : ℕ) := Fin k ⊕ ((Fin a ⊕ Fin b) ⊕ Fin r)

/-- Trace of a middle strand. The cell sits in columns `4*k` to `4*k+2`; bypasses are vertical. -/
@[expose] def MiddleContains {k a b r : ℕ} : Strand k a b r → Point → Prop
  | .inl i, p => p.1 = 4 * i.val ∧ p.2 ≤ 2
  | .inr (.inl e), p => 4 * k ≤ p.1 ∧ GridStar.Contains e (p.1 - 4 * k, p.2)
  | .inr (.inr j), p => p.1 = 4 * k + 4 + 4 * j.val ∧ p.2 ≤ 2

/-- The first endpoint of a middle strand. -/
@[expose] def middleStart {k a b r : ℕ} : Strand k a b r → Point
  | .inl i => (4 * i, 0)
  | .inr (.inl (.inl i)) => (i + 4 * k, 0)
  | .inr (.inl (.inr _)) => (GridStar.center a + 4 * k, 1)
  | .inr (.inr j) => (4 * k + 4 + 4 * j, 0)

/-- The last endpoint of a middle strand. -/
@[expose] def middleEnd {k a b r : ℕ} : Strand k a b r → Point
  | .inl i => (4 * i, 2)
  | .inr (.inl (.inl _)) => (GridStar.center a + 4 * k, 1)
  | .inr (.inl (.inr j)) => (j + 4 * k, 2)
  | .inr (.inr j) => (4 * k + 4 + 4 * j, 2)

/-- An explicit finite orthogonal path for each middle strand. -/
@[expose] def middlePath {k a b r : ℕ} (e : Strand k a b r) : Path (middleStart e) (middleEnd e) :=
  match e with
  | .inl i => .vertical (4 * i) 0 2 (by omega)
  | .inr (.inl (.inl i)) => (GridStar.path (Sum.inl i : Fin a ⊕ Fin b)).translate (4 * k) 0
  | .inr (.inl (.inr j)) => (GridStar.path (Sum.inr j : Fin a ⊕ Fin b)).translate (4 * k) 0
  | .inr (.inr j) => .vertical (4 * k + 4 + 4 * j) 0 2 (by omega)

/-- Each middle trace is the trace of its declared orthogonal path. -/
theorem middlePath_contains_iff {k a b r : ℕ} (e : Strand k a b r) (p : Point) :
    (middlePath e).Contains p ↔ MiddleContains e p := by
  rcases e with i | ((i | j) | j)
  · simp only [middlePath, Path.Contains, MiddleContains]
    omega
  · change ((GridStar.path (Sum.inl i : Fin a ⊕ Fin b)).translate (4 * k) 0).Contains p ↔ _
    rw [Path.contains_translate, GridStar.path_contains_iff]
    simp only [MiddleContains, Nat.sub_zero, Nat.zero_le, true_and]
  · change ((GridStar.path (Sum.inr j : Fin a ⊕ Fin b)).translate (4 * k) 0).Contains p ↔ _
    rw [Path.contains_translate, GridStar.path_contains_iff]
    simp only [MiddleContains, Nat.sub_zero, Nat.zero_le, true_and]
  · simp only [middlePath, Path.Contains, MiddleContains]
    omega

/-- Every middle strand lies between the two boundary rows. -/
theorem middle_row_le {k a b r : ℕ} (h : a + b = 3) {e : Strand k a b r} {p : Point}
    (hp : MiddleContains e p) : p.2 ≤ 2 := by
  rcases e with i | (e | j)
  · exact hp.2
  · exact (GridStar.bounded h hp.2).2
  · exact hp.2

/-- Distinct middle strands can meet only at the unique cell vertex. -/
theorem middle_intersection {k a b r : ℕ} (h : a + b = 3)
    {e f : Strand k a b r} (hef : e ≠ f) {p : Point}
    (he : MiddleContains e p) (hf : MiddleContains f p) :
    p = (4 * k + GridStar.center a, 1) ∧
      (∃ q, e = .inr (.inl q)) ∧ (∃ q, f = .inr (.inl q)) := by
  rcases e with i | (e | i) <;> rcases f with j | (f | j)
  · have hij : i.val ≠ j.val := fun hh => hef (congrArg Sum.inl (Fin.ext hh))
    simp only [MiddleContains] at he hf
    omega
  · have := i.isLt
    simp only [MiddleContains] at he hf
    omega
  · have := i.isLt
    simp only [MiddleContains] at he hf
    omega
  · have := j.isLt
    simp only [MiddleContains] at he hf
    omega
  · have hne : e ≠ f := fun hh => hef (congrArg (Sum.inr ∘ Sum.inl) hh)
    obtain hh := GridStar.intersection h hne he.2 hf.2
    have hx := congrArg Prod.fst hh
    have hy := congrArg Prod.snd hh
    refine ⟨Prod.ext ?_ hy, ⟨e, rfl⟩, ⟨f, rfl⟩⟩
    have := he.1
    omega
  · have hx := (GridStar.bounded h he.2).1
    simp only [MiddleContains] at he hf
    omega
  · have := j.isLt
    simp only [MiddleContains] at he hf
    omega
  · have hx := (GridStar.bounded h hf.2).1
    simp only [MiddleContains] at he hf
    omega
  · have hij : i.val ≠ j.val := fun hh =>
      hef (congrArg (Sum.inr ∘ Sum.inr) (Fin.ext hh))
    simp only [MiddleContains] at he hf
    omega

/-- Routing data for a layer with `k` prefix wires, `r` suffix wires, and a cell of arity three.
The middle band is `MiddleContains`; the two ordered routings attach to its ports. -/
structure Layer (k a b r : ℕ) where
  /-- Three incident ports. -/
  arity : a + b = 3
  /-- Standard input columns to the expanded input ports. -/
  upper : OrderedRouting (fun i : Fin (k + a + r) => 4 * i.val) (columns k a r)
  /-- Expanded output ports to standard output columns. -/
  lower : OrderedRouting (columns k b r) (fun i : Fin (k + b + r) => 4 * i.val)
/-- The positive height of a layer, including its two routing bands and its cell band. -/
@[expose] def Layer.height {k a b r : ℕ} (_L : Layer k a b r) : ℕ :=
  2 * (k + a + r + 1) + 2 + 2 * (k + b + r + 1)

/-- Every layer has room for the cell and both routing bands. -/
theorem Layer.height_pos {k a b r : ℕ} (L : Layer k a b r) : 0 < L.height := by
  unfold height
  omega

/-- Explicit orthogonal routing bands for an arbitrary three-port layer. -/
@[expose] def layer (k a b r : ℕ) (h : a + b = 3) : Layer k a b r where
  arity := h
  upper := route _ _ (fun _ _ h => Nat.mul_lt_mul_of_pos_left h (by decide))
    (columns_strictMono k a r (by omega))
  lower := route _ _ (columns_strictMono k b r (by omega))
    (fun _ _ h => Nat.mul_lt_mul_of_pos_left h (by decide))
/-- Each cell-band boundary point belongs to at most one middle strand. -/
theorem middle_boundary_unique {k a b r : ℕ} (h : a + b = 3) {e f : Strand k a b r}
    {x y : ℕ} (hy : y = 0 ∨ y = 2) (he : MiddleContains e (x, y))
    (hf : MiddleContains f (x, y)) : e = f := by
  by_contra hef
  have hp := (middle_intersection h hef he hf).1
  have hrow := congrArg Prod.snd hp
  rcases hy with rfl | rfl <;> cases hrow

/-- The upper routing and the cell band meet only at their common input port. -/
theorem Layer.upper_middle_intersection {k a b r : ℕ} (L : Layer k a b r)
    (i : Fin (k + a + r)) (e : Strand k a b r) (p : Point)
    (hu : L.upper.Contains i p) (hm : 2 * (k + a + r + 1) ≤ p.2 ∧
      MiddleContains e (p.1, p.2 - 2 * (k + a + r + 1))) :
    p.2 = 2 * (k + a + r + 1) ∧ p.1 = columns k a r i := by
  have hy := L.upper.row_le i hu
  have heq : p.2 = 2 * (k + a + r + 1) := by omega
  refine ⟨heq, ?_⟩
  exact (L.upper.bottom_iff i p.1).1 (heq ▸ hu)

/-- The cell band and the lower routing meet only at their common output port. -/
theorem Layer.middle_lower_intersection {k a b r : ℕ} (L : Layer k a b r)
    (e : Strand k a b r) (j : Fin (k + b + r)) (x y : ℕ)
    (hm : MiddleContains e (x, y))
    (hl : 2 ≤ y ∧ L.lower.Contains j (x, y - 2)) :
    y = 2 ∧ x = columns k b r j := by
  have hy := middle_row_le L.arity hm
  have heq : y = 2 := by omega
  refine ⟨heq, ?_⟩
  exact (L.lower.top_iff j x).1 (by simpa only [heq, Nat.sub_self] using hl.2)

/-- The upper and lower routing bands are separated by the cell's two rows. -/
theorem Layer.upper_lower_disjoint {k a b r : ℕ} (L : Layer k a b r)
    (i : Fin (k + a + r)) (p : Point) (hu : L.upper.Contains i p) :
    ¬2 * (k + a + r + 1) + 2 ≤ p.2 := by
  have := L.upper.row_le i hu
  omega

end Cslib.Complexity.NCL.GridLayout
