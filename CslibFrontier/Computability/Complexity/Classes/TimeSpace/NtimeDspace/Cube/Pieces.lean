/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Routing pieces and half-routings: definitions (§5.2–§5.3)

A *transport sum* counts, with weights, the maps from a list of numbered *sources* to a multiset
of interchangeable *targets* that meet every target multiplicity exactly. Every source and target
sits at a *place* and has a type; `R p i p' j` is the rule of a source of type `i` at `p` sent to
a target of type `j` at `p'`. We write the transport sum as a coefficient extraction:

  `transport src tgt R = [∏_{t ∈ tgt} X_t] ∏_{s ∈ src} (∑_{t} R s t • X_t)`,

where the product runs over the sources with multiplicity and the coefficient is that of the
monomial with the target multiplicities. Expanding the product, each term picks one target for
each source, and it contributes to that monomial exactly when every target receives its
multiplicity; so the coefficient is the sum, over the maps of the paper (sources numbered, targets
interchangeable), of the products of the rules. Coefficients live in the Laurent polynomials
`ℤ[z, z⁻¹]`, with `z = T 1`.

* `Corner`: the four corners `x, y` (upper row) and `u, v` (lower row) of a rectangle;
  `x, v` and `y, u` are the diagonals.
* `rule`: the rules of a routing (§5.2): a diagonal joins equal types with rule `1`; a side joins
  a type `i` at `x` or `v` to a type `j` at `y` or `u` with `R_xu = (1 - z²) C_{i,j}`,
  `R_vy = C_{i,j}`, `R_xy = (1 - z⁻²) C̄_{i,j}` and `R_vu = C̄_{i,j}`, where `C̄(z) = C(1/z)`.
  A source and a target at the same corner have rule `0`.
* `piece v`: `Π_{x,y,u,v}(z)` for the views `v : Corner → Label` (each view is `(out, in)`, the
  requests the corner sends and receives). Its coefficient of `z^k` is the piece `Π_k`.
* `nUp x y m` and `nDown u v m`: the half-routing sums `N↑(x, y; m)` and `N↓(u, v; m)` of §5.3,
  for a message `m = (η, ζ)` (`η` sent downward, `ζ` upward). A request crossing the row cut meets
  the message at an intermediate type `n`, with the half-rule `(1 - z²) C_{i,n}` at `x`, `[i = n]`
  at `y` and at `u`, and `C_{i,n}` at `v`.
* `transposeView`: the views of the transposed rectangle `(x, u, y, v)`.
* `crossing v`: the crossing `[x = v][y = u]`, where `[x = v]` means `out_x = in_v ∧ in_x = out_v`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open MvPolynomial LaurentPolynomial

/-- The coefficient ring `ℤ[z, z⁻¹]`. -/
abbrev Lp := LaurentPolynomial ℤ

/-! ### Transport sums -/

section Transport

variable {P : Type} [DecidableEq P]

/-- The linear form of a source: `∑_{t ∈ supp tgt} R s t • X_t`. -/
noncomputable def srcForm (tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → Lp) (s : P × ℕ) :
    MvPolynomial (P × ℕ) Lp :=
  ∑ t ∈ tgt.toFinset, MvPolynomial.C (R s.1 s.2 t.1 t.2) * X t

/-- **A transport sum**: the sum over the maps from the sources `src` (numbered) to the targets
`tgt` (interchangeable) meeting every target multiplicity, of the product of the rules, written as
the coefficient of the target monomial in the product of the source forms. -/
noncomputable def transport (src tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → Lp) : Lp :=
  ((src.map (srcForm tgt R)).prod).coeff (Multiset.toFinsupp tgt)

end Transport

/-! ### Corners and rules -/

/-- The corners of a rectangle: `x, y` in the upper row, `u, v` in the lower row; `x, v` and
`y, u` are the diagonals. -/
inductive Corner | x | y | u | v
  deriving DecidableEq, Repr

/-- `f̄(z) = f(1/z)`. -/
noncomputable def bar (f : Lp) : Lp := invert f

/-- `1 - z²`. -/
noncomputable def oneSubZ2 : Lp := 1 - T 2

/-- `1 - z⁻²`. -/
noncomputable def oneSubZm2 : Lp := 1 - T (-2)

/-- `[i = j]` as a Laurent polynomial. -/
noncomputable def eqL (i j : ℕ) : Lp := if i = j then 1 else 0

/-- **The rules of a routing** (§5.2), for a source of type `i` at corner `c` and a target of type
`j` at corner `c'`. -/
noncomputable def rule : Corner → ℕ → Corner → ℕ → Lp
  | .x, i, .v, j | .v, i, .x, j | .y, i, .u, j | .u, i, .y, j => eqL i j
  | .x, i, .u, j => oneSubZ2 * C i j
  | .u, j, .x, i => oneSubZ2 * C i j
  | .v, i, .y, j => C i j
  | .y, j, .v, i => C i j
  | .x, i, .y, j => oneSubZm2 * bar (C i j)
  | .y, j, .x, i => oneSubZm2 * bar (C i j)
  | .v, i, .u, j => bar (C i j)
  | .u, j, .v, i => bar (C i j)
  | _, _, _, _ => 0

/-- The requests of a corner's view as located sources (`out`) or targets (`in`). -/
def located {P : Type} (p : P) (σ : Multiset ℕ) : Multiset (P × ℕ) := σ.map fun i => (p, i)

/-- All sources of the views. -/
def sourcesOf (V : Corner → Label) : Multiset (Corner × ℕ) :=
  located .x (V .x).1 + located .y (V .y).1 + located .u (V .u).1 + located .v (V .v).1

/-- All targets of the views. -/
def targetsOf (V : Corner → Label) : Multiset (Corner × ℕ) :=
  located .x (V .x).2 + located .y (V .y).2 + located .u (V .u).2 + located .v (V .v).2

/-- **The routing polynomial** `Π_{x,y,u,v}(z)`: the sum over routings of the products of their
rules. Its coefficient of `z^k` is the piece `Π_k`. -/
noncomputable def piece (V : Corner → Label) : Lp := transport (sourcesOf V) (targetsOf V) rule

/-- The crossing `[x = v][y = u]`. -/
def crossing (V : Corner → Label) : Prop :=
  (V .x).1 = (V .v).2 ∧ (V .x).2 = (V .v).1 ∧ (V .y).1 = (V .u).2 ∧ (V .y).2 = (V .u).1

instance (V : Corner → Label) : Decidable (crossing V) := by unfold crossing; infer_instance

/-- Exchanging the corners `y` and `u`: transposing the rectangle (reflecting it in `xv`). -/
def swapYU : Corner → Corner
  | .y => .u
  | .u => .y
  | c => c

/-- The views of the transposed rectangle `(x, u, y, v)`. -/
def transposeView (V : Corner → Label) : Corner → Label := V ∘ swapYU

/-- The views `(x, y, u, v)` from four labels. -/
def views (x y u v : Label) : Corner → Label
  | .x => x
  | .y => y
  | .u => u
  | .v => v

/-! ### Half-routings (§5.3) -/

/-- The places of a half-routing: a corner of its row (`some c`) or the cut (`none`), where the
requests of the message are met. -/
abbrev HPlace := Option Corner

/-- The rules of an upper half-routing for the row `x, y`: `R_xy` between `x` and `y`; between a
corner and the cut, the half-rule `(1 - z²) C_{i,n}` at `x` and the copy `[i = n]` at `y`. -/
noncomputable def upRule : HPlace → ℕ → HPlace → ℕ → Lp
  | some .x, i, some .y, j => oneSubZm2 * bar (C i j)
  | some .y, j, some .x, i => oneSubZm2 * bar (C i j)
  | some .x, i, none, n => oneSubZ2 * C i n
  | none, n, some .x, i => oneSubZ2 * C i n
  | some .y, i, none, n => eqL i n
  | none, n, some .y, i => eqL i n
  | _, _, _, _ => 0

/-- The rules of a lower half-routing for the row `u, v`: `R_vu` between `v` and `u`; between a
corner and the cut, the half-rule `C_{i,n}` at `v` and the copy `[i = n]` at `u`. -/
noncomputable def downRule : HPlace → ℕ → HPlace → ℕ → Lp
  | some .v, i, some .u, j => bar (C i j)
  | some .u, j, some .v, i => bar (C i j)
  | some .v, i, none, n => C i n
  | none, n, some .v, i => C i n
  | some .u, i, none, n => eqL i n
  | none, n, some .u, i => eqL i n
  | _, _, _, _ => 0

/-- **The upper half-routing sum** `N↑(x, y; m)` for a message `m = (η, ζ)`: the sources are the
outgoing requests of `x` and `y` and the requests of `ζ` (sent upward, numbered); the targets are
the incoming requests of `x` and `y` and the requests of `η` (sent downward, interchangeable). -/
noncomputable def nUp (x y m : Label) : Lp :=
  transport (located (some .x) x.1 + located (some .y) y.1 + located none m.2)
    (located (some .x) x.2 + located (some .y) y.2 + located none m.1) upRule

/-- **The lower half-routing sum** `N↓(u, v; m)`: the sources are the outgoing requests of `u`
and `v` and the requests of `η`; the targets are the incoming requests of `u` and `v` and the
requests of `ζ`. -/
noncomputable def nDown (u v m : Label) : Lp :=
  transport (located (some .u) u.1 + located (some .v) v.1 + located none m.1)
    (located (some .u) u.2 + located (some .v) v.2 + located none m.2) downRule

end Cslib.Complexity.NtimeDspace.Cube
