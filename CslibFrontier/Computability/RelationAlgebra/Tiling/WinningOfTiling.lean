/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationAlgebra.Tiling.Frame
public import CslibFrontier.Computability.WangTile.EveryTileOccurs
public import CslibFrontier.Foundations.RelationAlgebra.Game
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module

/-!
# Tilings give a winning strategy

Theorem 4 of [HirschHodkinson2001], Section 6: if every tile of a list is at the origin of a
tiling by the list, and the first tile matches itself, then ∃ has a winning strategy in the game
of `RA(τ)`.

## The strategy

By `AtomFrame.HasWinningStrategy.of_forall_exists_comap_castSucc` it is enough that ∃ answers the
moves of ∀ that have no witness yet, each by adding one node. On the edges from the new node that
∀ leaves unlabelled she puts the atoms of the source, Section 6.1:

* a white atom between two nodes of one kind;
* a tile atom between a `1`-node and a `2`-node that some `0`-node sees along green edges, and
  a white atom between two that no `0`-node sees;
* `u`, `v` or a white atom on an edge from a `0`-node.

The conditions for `u` and `v`, and the bookkeeping behind the choice of tile atoms, are organized
differently from the source. For each `0`-node `h` and each axis, ∃ divides the nodes that `h`
sees along green edges into classes, and gives each of them an integer that increases by one
along every step `+1` between two of them: a new node joins the class of the node to which a step
joins it, and otherwise starts a class. She puts `u` on the edge from `h` to a node joined by
steps to two distinct nodes of one class under `h`; the source asks for a cycle of steps through
the node whose other nodes `h` sees. She puts `v` on the edge from `h` to a node joined by tile
edges to two distinct nodes of one class under `h`; the source asks for a chain of steps between
nodes that `h` sees, to the two ends of which tile edges join the node. For `v` the edges that
count are those that are tile edges once the round is over, as in the correction to case II(2)(c)
printed at the end of the authors' copy of the source under "Added after posting".

Each tile edge is placed at a cell of one of the given tilings and is labelled by the tile there.
A new tile edge is placed next to the tile edges that constrain it, and in the constant tiling by
the tile at position `0` when none does. That the constraints agree (`Move.cand_unique`) takes the
place of the source's Lemma 5 and of the choice of co-ordinates in its Section 6.5.

## The invariant

The source argues about the order in which the nodes of a play were added, and keeps conditions
T1–T3 on the tile edges linked through triangles that ∀ did not build. Here the facts that those
arguments give are instead part of an invariant `Good` of a single network with its bookkeeping,
and no history of the play is kept:

* `Good.u_class`: a node joined by steps to two distinct nodes of one class under `h` is seen by
  `h` along a green edge or along `u`. With rule 3 it does the work of the source's Lemma 6.
* `Good.v_class`: a node joined by tile edges to two distinct nodes of one class under `h` is seen
  by `h` along a green edge or along `v`. With rule 4 it gives the claim in the source's proof of
  Lemma 5(2), which is where the correction is needed.
* `Good.apex_unique`: no second `0`-node sees two distinct nodes of one class under `h`. Its proof
  uses Convention 1(2) of the source, that ∀ makes no move that has a witness.
* `Good.cell_class`: the tile edges from the nodes of one class under `h` to a node that `h` sees
  lie in one tiling, along a row or a column, at the places given by the integers of the class.
  This takes the place of T1 and T2.

Each is preserved because ∀ labels at most two edges from the new node (`Move.isPar_three`), and
∃ puts no green atom and no step on an edge. The two axes are treated at once: rules 2–4 and
their duals are the instances of `Rule.cases` for the two axes.

## Main results

* `Cslib.RelationAlgebra.hasWinningStrategy_tilingFrame`: Theorem 4 of the source.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

namespace Cslib.RelationAlgebra

open WangTile

namespace Tiling

open Atom

variable {ι : Type*} {L : List WangTile} {D : Type}

/-! ### Axes and shapes of atoms -/

/-- The axis other than `d`. -/
private def Axis.other : Axis → Axis
  | .one => .two
  | .two => .one

@[simp]
private theorem Axis.other_other (d : Axis) : d.other.other = d := by cases d <;> rfl

/-- The direction of the tile atoms on the edges that start at a `d`-node: `T₁₂ⁱ` starts at a
`1`-node and its converse at a `2`-node. -/
private def Axis.tileDir : Axis → Direction
  | .one => .forward
  | .two => .reverse

/-- The unit vector of the plane along an axis. -/
private def Axis.vec : Axis → ℤ × ℤ
  | .one => (1, 0)
  | .two => (0, 1)

/-- The colour of the edge of a tile that faces backwards along an axis: left or bottom. -/
private def Axis.back : Axis → WangTile → ℕ
  | .one, t => t.left
  | .two, t => t.bottom

/-- The colour of the edge of a tile that faces forwards along an axis: right or top. -/
private def Axis.front : Axis → WangTile → ℕ
  | .one, t => t.right
  | .two, t => t.top

/-- The steps `±1₁` and `±1₂`. -/
private def Atom.IsStep : Atom ι → Prop
  | step _ _ => True
  | _ => False

/-- The tile atoms and their converses. -/
private def Atom.IsTile : Atom ι → Prop
  | tile _ _ => True
  | _ => False

/-- The displacement of a step: `1` for `+1_d`, `-1` for `-1_d`, and `0` for other atoms. -/
private def Atom.sgn : Atom ι → ℤ
  | step _ .forward => 1
  | step _ .reverse => -1
  | _ => 0

private theorem Atom.isStep_iff {a : Atom ι} : a.IsStep ↔ ∃ d o, a = step d o := by
  cases a <;> simp [Atom.IsStep]

private theorem Atom.isTile_iff {a : Atom ι} : a.IsTile ↔ ∃ i o, a = tile i o := by
  cases a <;> simp [Atom.IsTile]

@[simp]
private theorem Atom.isStep_conv {a : Atom ι} : a.conv.IsStep ↔ a.IsStep := by
  cases a <;> exact .rfl

@[simp]
private theorem Atom.isTile_conv {a : Atom ι} : a.conv.IsTile ↔ a.IsTile := by
  cases a <;> exact .rfl

@[simp]
private theorem Atom.isUnit_unit (i : Kind) : (unit i : Atom ι).IsUnit := trivial

private theorem Atom.IsUnit.eq_unit {a : Atom ι} (h : a.IsUnit) : a = unit a.src := by
  cases a <;> first | rfl | exact h.elim

private theorem Atom.conv_eq_iff {a b : Atom ι} : a.conv = b ↔ a = b.conv :=
  ⟨fun h => by rw [← h, conv_conv], fun h => by rw [h, conv_conv]⟩

@[simp]
private theorem Axis.kind_inj {d e : Axis} : d.kind = e.kind ↔ d = e := by
  cases d <;> cases e <;> simp [Axis.kind]

@[simp]
private theorem Axis.kind_ne_zero (d : Axis) : d.kind ≠ .zero := by cases d <;> simp [Axis.kind]

@[simp]
private theorem Axis.zero_ne_kind (d : Axis) : Kind.zero ≠ d.kind := by
  cases d <;> simp [Axis.kind]

@[simp]
private theorem Axis.other_ne_self (d : Axis) : d.other ≠ d := by cases d <;> simp [Axis.other]

@[simp]
private theorem Axis.self_ne_other (d : Axis) : d ≠ d.other := by cases d <;> simp [Axis.other]

@[simp] private theorem Atom.src_white (i j : Kind) : (white i j : Atom ι).src = i := rfl
@[simp] private theorem Atom.tgt_white (i j : Kind) : (white i j : Atom ι).tgt = j := rfl
@[simp] private theorem Atom.src_green_forward (d : Axis) :
    (green d .forward : Atom ι).src = .zero := rfl
@[simp] private theorem Atom.tgt_green_forward (d : Axis) :
    (green d .forward : Atom ι).tgt = d.kind := rfl
@[simp] private theorem Atom.src_green_reverse (d : Axis) :
    (green d .reverse : Atom ι).src = d.kind := rfl
@[simp] private theorem Atom.tgt_green_reverse (d : Axis) :
    (green d .reverse : Atom ι).tgt = .zero := rfl
@[simp] private theorem Atom.src_u_forward (d : Axis) : (u d .forward : Atom ι).src = .zero := rfl
@[simp] private theorem Atom.tgt_u_forward (d : Axis) : (u d .forward : Atom ι).tgt = d.kind := rfl
@[simp] private theorem Atom.src_u_reverse (d : Axis) : (u d .reverse : Atom ι).src = d.kind := rfl
@[simp] private theorem Atom.tgt_u_reverse (d : Axis) : (u d .reverse : Atom ι).tgt = .zero := rfl
@[simp] private theorem Atom.src_v_forward (d : Axis) : (v d .forward : Atom ι).src = .zero := rfl
@[simp] private theorem Atom.tgt_v_forward (d : Axis) : (v d .forward : Atom ι).tgt = d.kind := rfl
@[simp] private theorem Atom.src_v_reverse (d : Axis) : (v d .reverse : Atom ι).src = d.kind := rfl
@[simp] private theorem Atom.tgt_v_reverse (d : Axis) : (v d .reverse : Atom ι).tgt = .zero := rfl
@[simp] private theorem Atom.src_step (d : Axis) (o : Direction) :
    (step d o : Atom ι).src = d.kind := rfl
@[simp] private theorem Atom.tgt_step (d : Axis) (o : Direction) :
    (step d o : Atom ι).tgt = d.kind := by cases o <;> rfl
@[simp] private theorem Atom.src_tile (i : ι) (d : Axis) :
    (tile i d.tileDir : Atom ι).src = d.kind := by cases d <;> rfl
@[simp] private theorem Atom.tgt_tile (i : ι) (d : Axis) :
    (tile i d.tileDir : Atom ι).tgt = d.other.kind := by cases d <;> rfl

/-- A tile atom starts at the nodes of some axis. -/
private theorem Direction.exists_tileDir (o : Direction) : ∃ d : Axis, o = d.tileDir := by
  cases o
  · exact ⟨.one, rfl⟩
  · exact ⟨.two, rfl⟩

/-! ### The rules -/

/-- The four shapes of the triangles listed in `Rule`, with rules 2–4 and their duals stated once
for the two axes. -/
private theorem Rule.cases {r s t : Atom (Fin L.length)} (h : Rule L r s t) :
    (r = green .one .reverse ∧ s = green .two .forward ∧ t = white .one .two) ∨
    (∃ d i j, r = tile i d.tileDir ∧ s = tile j d.tileDir.flip ∧ t = step d .reverse ∧
      d.back L[i] ≠ d.front L[j]) ∨
    (∃ d i, r = u d .reverse ∧ s = green d.other .forward ∧ t = tile i d.tileDir ∧ i.val ≠ 0) ∨
    (∃ d o, r = v d .reverse ∧ s = green d .forward ∧ t = step d o) := by
  unfold Rule at h
  split at h
  · exact .inl ⟨rfl, rfl, rfl⟩
  · exact .inr (.inl ⟨.one, _, _, rfl, rfl, rfl, h⟩)
  · exact .inr (.inl ⟨.two, _, _, rfl, rfl, rfl, h⟩)
  · exact .inr (.inr (.inl ⟨.one, _, rfl, rfl, rfl, h⟩))
  · exact .inr (.inr (.inl ⟨.two, _, rfl, rfl, rfl, h⟩))
  · exact .inr (.inr (.inr ⟨.one, _, rfl, rfl, rfl⟩))
  · exact .inr (.inr (.inr ⟨.two, _, rfl, rfl, rfl⟩))
  · exact h.elim

private theorem Rule.not_isUnit {r s t : Atom (Fin L.length)} (h : Rule L r s t) :
    ¬r.IsUnit ∧ ¬s.IsUnit ∧ ¬t.IsUnit := by
  obtain ⟨rfl, rfl, rfl⟩ | ⟨d, i, j, rfl, rfl, rfl, -⟩ | ⟨d, i, rfl, rfl, rfl, -⟩ |
    ⟨d, o, rfl, rfl, rfl⟩ := h.cases <;> simp [Atom.IsUnit]

private theorem rule_u {d : Axis} {i : Fin L.length} (hi : i.val ≠ 0) :
    Rule L (u d .reverse) (green d.other .forward) (tile i d.tileDir) := by
  cases d <;> simpa [Rule, Axis.other, Axis.tileDir] using hi

private theorem rule_v (d : Axis) (o : Direction) :
    Rule L (v d .reverse) (green d .forward) (step d o) := by
  cases d <;> simp [Rule]

/-! ### Typed labellings -/

/-- A labelling of the ordered pairs of nodes by atoms is typed when the kind of node at which a
label starts depends only on the first node, and reversing an edge takes the converse. The kind
of the node `x` is then `(lab x x).src`. -/
private structure Typed (lab : D → D → Atom ι) : Prop where
  src_eq (x y : D) : (lab x y).src = (lab x x).src
  conv_lab (x y : D) : (lab x y).conv = lab y x

private theorem Typed.tgt_eq {lab : D → D → Atom ι} (K : Typed lab) (x y : D) :
    (lab x y).tgt = (lab y y).src := by
  rw [Atom.tgt, K.conv_lab, K.src_eq]

private theorem Typed.src_of_eq {lab : D → D → Atom ι} (K : Typed lab) {x y : D} {a : Atom ι}
    (h : lab x y = a) : (lab x x).src = a.src := by
  rw [← h, K.src_eq x y]

private theorem Typed.tgt_of_eq {lab : D → D → Atom ι} (K : Typed lab) {x y : D} {a : Atom ι}
    (h : lab x y = a) : (lab y y).src = a.tgt := by
  rw [← h, K.tgt_eq]

private theorem Typed.eq_conv {lab : D → D → Atom ι} (K : Typed lab) {x y : D} {a : Atom ι}
    (h : lab x y = a) : lab y x = a.conv := by
  rw [← h, K.conv_lab]

/-! ### Annotated labellings and the invariant -/

variable (L) in
/-- The place of a tile edge in a tiling: the position `seed` of `L` whose tiling is used, and a
cell of the plane. The cell is only meaningful when the seed is not `0`. -/
private structure Cell where
  /-- The tiling used is the one with the tile at this position of `L` at the origin. -/
  seed : Fin L.length
  /-- The cell of the plane. -/
  pos : ℤ × ℤ

variable (L) in
/-- A tiling of the plane by positions of `L` for each position `σ`, with `σ` at the origin, the
one for `0` being constant. -/
private structure Tilings [NeZero L.length] where
  /-- The tiling for the position `σ`. -/
  til : Fin L.length → ℤ × ℤ → Fin L.length
  til_zero (c : ℤ × ℤ) : til 0 c = 0
  til_origin (σ : Fin L.length) : til σ 0 = σ
  til_match (σ : Fin L.length) (c : ℤ × ℤ) (d : Axis) :
    d.front L[til σ c] = d.back L[til σ (c + d.vec)]

/-- The position of `L` at a cell of a tiling. -/
private def Tilings.idx [NeZero L.length] (T : Tilings L) (m : Cell L) : Fin L.length :=
  T.til m.seed m.pos

variable (L D) in
/-- A labelling of the ordered pairs of nodes by atoms, with the bookkeeping that ∃ keeps.

For a `0`-node `h` and an axis `d`, the `d`-nodes `a` with `lab h a = g₀d` are divided into
classes, `root h a` naming the class of `a`, and `pot h a` is an integer that increases by one
along each step `+1_d` between two of them. Each tile edge has a `cell`. -/
private structure Ann where
  /-- The atom on the edge from the first node to the second. -/
  lab : D → D → Atom (Fin L.length)
  /-- `root h a` names the class of `a` among the nodes that `h` sees along a green edge. -/
  root : D → D → D
  /-- `pot h a` is the place of `a` in its class under `h`. -/
  pot : D → D → ℤ
  /-- The place in a tiling of the tile edge between two nodes. -/
  cell : D → D → Cell L

/-- Two distinct nodes of one class under the `0`-node `h`. -/
private structure Twin (lab : D → D → Atom (Fin L.length)) (root : D → D → D) (d : Axis)
    (h a a' : D) : Prop where
  ne : a ≠ a'
  left : lab h a = green d .forward
  right : lab h a' = green d .forward
  root_eq : root h a = root h a'

/-- The condition under which ∃ labels the edge from the `0`-node `h` to `b` with `u₀d`: two
distinct nodes of one class under `h` are joined to `b` by steps. -/
private def UCond (lab : D → D → Atom (Fin L.length)) (root : D → D → D) (d : Axis)
    (h b : D) : Prop :=
  ∃ a a', Twin lab root d h a a' ∧ (lab a b).IsStep ∧ (lab a' b).IsStep

/-- The condition under which ∃ labels the edge from the `0`-node `h` to `y` with a `v` atom: two
distinct nodes of one class under `h` are joined to `y` by tile edges, `wt` saying which edges
are tile edges. -/
private def VCond (lab : D → D → Atom (Fin L.length)) (root : D → D → D) (wt : D → D → Prop)
    (d : Axis) (h y : D) : Prop :=
  ∃ a a', Twin lab root d h a a' ∧ wt a y ∧ wt a' y

/-- The invariant of ∃'s strategy. -/
private structure Good [NeZero L.length] (T : Tilings L) (S : Ann L D) : Prop where
  typed : Typed S.lab
  isUnit_iff (x y : D) : (S.lab x y).IsUnit ↔ x = y
  rule_free (x y w : D) : ¬Rule L (S.lab x y) (S.lab y w) (S.lab x w)
  /-- A step between two nodes that `h` sees joins nodes of one class, and raises `pot`. -/
  step_class {h a b : D} {d e : Axis} : S.lab h a = green d .forward →
    S.lab h b = green d .forward → S.lab a b = step e .forward →
    S.root h a = S.root h b ∧ S.pot h b = S.pot h a + 1
  /-- A node joined by steps to two nodes of one class under `h` is seen by `h` along a green
  edge or along `u`. -/
  u_class {h b : D} {d : Axis} : UCond S.lab S.root d h b →
    S.lab h b = green d .forward ∨ S.lab h b = u d .forward
  /-- A node joined by tile edges to two nodes of one class under `h` is seen by `h` along a
  green edge or along `v`. -/
  v_class {h y : D} {d : Axis} : VCond S.lab S.root (fun a y => (S.lab a y).IsTile) d h y →
    S.lab h y = green d.other .forward ∨ S.lab h y = v d.other .forward
  /-- No second `0`-node sees two nodes of one class under `h`. -/
  apex_unique {h h' a a' : D} {d : Axis} : Twin S.lab S.root d h a a' →
    S.lab h' a = green d .forward → S.lab h' a' = green d .forward → h = h'
  cell_symm (x y : D) : S.cell x y = S.cell y x
  /-- A tile edge is labelled by the position of `L` at its cell. -/
  tile_idx {x y : D} {i : Fin L.length} {o : Direction} : S.lab x y = tile i o →
    i = T.idx (S.cell x y)
  /-- The tile edges from the nodes of one class under `h` to a node that `h` sees lie in one
  tiling, at the cells of a row or column given by `pot`. -/
  cell_class {h a b y : D} {d : Axis} : S.lab h a = green d .forward →
    S.lab h b = green d .forward → S.lab h y = green d.other .forward →
    S.root h a = S.root h b → (S.cell b y).seed = (S.cell a y).seed ∧
      ((S.cell a y).seed ≠ 0 →
        (S.cell b y).pos = (S.cell a y).pos + (S.pot h b - S.pot h a) • d.vec)

section

variable [NeZero L.length] {T : Tilings L} {S : Ann L D}

private theorem Good.sgn_self (hS : Good T S) (x : D) : (S.lab x x).sgn = 0 := by
  rw [((hS.isUnit_iff x x).mpr rfl).eq_unit]
  rfl

private theorem Good.ne_of_isStep (hS : Good T S) {x y : D} (h : (S.lab x y).IsStep) :
    x ≠ y := fun hxy => by
  obtain ⟨d, o, hd⟩ := Atom.isStep_iff.mp h
  have h₁ := (hS.isUnit_iff x y).mpr hxy
  rw [hd] at h₁
  exact h₁

private theorem Good.ne_of_isTile (hS : Good T S) {x y : D} (h : (S.lab x y).IsTile) :
    x ≠ y := fun hxy => by
  obtain ⟨d, o, hd⟩ := Atom.isTile_iff.mp h
  have h₁ := (hS.isUnit_iff x y).mpr hxy
  rw [hd] at h₁
  exact h₁

private theorem Good.ne_of_green (hS : Good T S) {x y : D} {d : Axis} {o : Direction}
    (h : S.lab x y = green d o) : x ≠ y := fun hxy => by
  have h₁ := (hS.isUnit_iff x y).mpr hxy
  rw [h] at h₁
  exact h₁

/-- The atomic network of a labelling that satisfies the invariant. -/
private def Good.network (hS : Good T S) : AtomicNetwork (tilingFrame L) D :=
  Tiling.network S.lab (fun x => (S.lab x x).src) hS.isUnit_iff hS.typed.conv_lab
    hS.typed.src_eq hS.rule_free

/-- By rule 1, the edge between two nodes of different axes seen by one node is a tile edge. -/
private theorem Good.isTile_of_green (hS : Good T S) {h x y : D} {d : Axis}
    (hx : S.lab h x = green d .forward)
    (hy : S.lab h y = green d.other .forward) : (S.lab x y).IsTile := by
  have key {x y : D} (hx : S.lab h x = green .one .forward)
      (hy : S.lab h y = green .two .forward) : (S.lab x y).IsTile := by
    have hc : Cycle L (S.lab x h) (S.lab h y) (S.lab x y) := hS.network.label_mem_cycles x h y
    rw [hS.typed.eq_conv hx, hy] at hc
    obtain ⟨i, hi⟩ := hc.exists_eq_tile
    simp [hi, Atom.IsTile]
  cases d with
  | one => exact key hx hy
  | two =>
    have ht := key hy hx
    rwa [← hS.typed.conv_lab, Atom.isTile_conv] at ht

/-- The tiles at two cells of one tiling that are adjacent along an axis match. -/
private theorem Tilings.front_eq_back (T : Tilings L) {m m' : Cell L}
    {d : Axis} (hs : m'.seed = m.seed) (hp : m.seed ≠ 0 → m'.pos = m.pos + d.vec) :
    d.front L[T.idx m] = d.back L[T.idx m'] := by
  have key (a b : Fin L.length) (ha : T.idx m = a) (hb : T.idx m' = b)
      (h : d.front L[a] = d.back L[b]) : d.front L[T.idx m] = d.back L[T.idx m'] := by
    subst ha hb
    exact h
  refine key _ _ rfl ?_ (T.til_match m.seed m.pos d)
  by_cases h0 : m.seed = 0
  · simp [Tilings.idx, hs, h0, T.til_zero]
  · simp [Tilings.idx, hs, hp h0]

/-! ### The opening positions -/

/-- The labelling of two nodes joined by an edge with a given atom. -/
private def Ann.pair (a : Atom (Fin L.length)) : Ann L Bool where
  lab
    | false, false => unit a.src
    | false, true => a
    | true, false => a.conv
    | true, true => unit a.tgt
  root _ y := y
  pot _ _ := 0
  cell _ _ :=
    match a with
    | tile j _ => ⟨j, 0⟩
    | _ => ⟨0, 0⟩

private theorem Ann.good_pair {a : Atom (Fin L.length)} (ha : ¬a.IsUnit) :
    Good T (Ann.pair a) where
  typed :=
    { src_eq x y := by cases x <;> cases y <;> rfl
      conv_lab x y := by cases x <;> cases y <;> first | rfl | exact conv_conv a }
  isUnit_iff x y := by cases x <;> cases y <;> simp [Ann.pair, ha]
  rule_free x y w h := by
    obtain ⟨h₁, h₂, h₃⟩ := h.not_isUnit
    cases x <;> cases y <;> cases w <;> simp [Ann.pair] at h₁ h₂ h₃
  step_class {h x y} _ _ h₁ h₂ h₃ := by
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at h₁ h₂ h₃
  u_class {h b} _ := by
    rintro ⟨x, y, ⟨hne, h₁, h₂, -⟩, -, -⟩
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at hne h₁ h₂
  v_class {h b} _ := by
    rintro ⟨x, y, ⟨hne, h₁, h₂, -⟩, -, -⟩
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at hne h₁ h₂
  apex_unique {h h' x y} _ := by
    rintro ⟨hne, h₁, h₂, -⟩ - -
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at hne h₁ h₂
  cell_symm _ _ := rfl
  tile_idx {x y i o} h := by
    cases x <;> cases y <;> cases a <;> cases o <;>
      simp_all [Ann.pair, Atom.conv, Direction.flip, Tilings.idx, T.til_origin]
  cell_class {h x y z} _ h₁ h₂ h₃ _ := by
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at h₁ h₂ ⊢

/-- The labelling of a single node with a unit on its loop. -/
private def Ann.single (i : Kind) : Ann L Unit where
  lab _ _ := unit i
  root _ y := y
  pot _ _ := 0
  cell _ _ := ⟨0, 0⟩

private theorem Ann.good_single (i : Kind) : Good T (Ann.single i) where
  typed := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  isUnit_iff _ _ := by simp [Ann.single]
  rule_free _ _ _ h := h.not_isUnit.1 trivial
  step_class h := by simp [Ann.single] at h
  u_class := by
    rintro _ _ _ ⟨x, y, ⟨-, h, -, -⟩, -, -⟩
    simp [Ann.single] at h
  v_class := by
    rintro _ _ _ ⟨x, y, ⟨-, h, -, -⟩, -, -⟩
    simp [Ann.single] at h
  apex_unique := by
    rintro _ _ _ _ _ ⟨-, h, -, -⟩ - -
    simp [Ann.single] at h
  cell_symm _ _ := rfl
  tile_idx h := by simp [Ann.single] at h
  cell_class h := by simp [Ann.single] at h

end

/-! ### Moves -/

variable (S : Ann L D) in
/-- A move of ∀ that has no witness yet: two nodes `p`, `q` and two atoms `a`, `b` whose product
lies above the label of `(p, q)`. -/
private structure Move where
  /-- The first node of the edge picked. -/
  p : D
  /-- The second node of the edge picked. -/
  q : D
  /-- The atom demanded on the edge from `p` to the new node. -/
  a : Atom (Fin L.length)
  /-- The atom demanded on the edge from the new node to `q`. -/
  b : Atom (Fin L.length)
  legal : Cycle L a b (S.lab p q)
  fresh (w : D) : S.lab p w = a → S.lab w q ≠ b

namespace Move

variable {S : Ann L D} (M : Move S)

/-- The kind of the new node. -/
private def kind : Kind := M.a.tgt

/-- The nodes picked by ∀, whose edges to the new node he labels. -/
private def IsPar (x : D) : Prop := x = M.p ∨ x = M.q

open Classical in
/-- The atom on the edge from an old node to the new node before ∃ labels the edges that ∀ left
unlabelled: the atom demanded by ∀ on the edges from `p` and `q`, and a white atom, which stands
for no label, on the others. -/
private noncomputable def par (x : D) : Atom (Fin L.length) :=
  if x = M.p then M.a else if x = M.q then M.b.conv else white (S.lab x x).src M.kind

private theorem par_p : M.par M.p = M.a := by simp [par]

private theorem par_of_not_isPar {x : D} (h : ¬M.IsPar x) :
    M.par x = white (S.lab x x).src M.kind := by
  have hp : x ≠ M.p := fun hp => h (.inl hp)
  have hq : x ≠ M.q := fun hq => h (.inr hq)
  simp [par, hp, hq]

private theorem isPar_of_par {x : D} (h : ∀ i j, M.par x ≠ white i j) : M.IsPar x := by
  by_contra hx
  exact h _ _ (M.par_of_not_isPar hx)

private theorem isPar_of_isStep {x : D} (h : (M.par x).IsStep) : M.IsPar x :=
  M.isPar_of_par fun i j hw => by simp [hw, Atom.IsStep] at h

private theorem isPar_of_isTile {x : D} (h : (M.par x).IsTile) : M.IsPar x :=
  M.isPar_of_par fun i j hw => by simp [hw, Atom.IsTile] at h

private theorem isPar_of_green {x : D} {d : Axis} {o : Direction} (h : M.par x = green d o) :
    M.IsPar x :=
  M.isPar_of_par fun i j hw => by simp [hw] at h

/-- ∀ labels at most two edges to the new node. -/
private theorem isPar_three {x y w : D} (hx : M.IsPar x) (hy : M.IsPar y) (hw : M.IsPar w) :
    x = y ∨ x = w ∨ y = w := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hw with rfl | rfl <;> simp

/-- Among three of the nodes picked by ∀, two that carry different atoms leave no room for a
third. -/
private theorem eq_of_isPar {x y w : D} (hx : M.IsPar x) (hy : M.IsPar y) (hw : M.IsPar w)
    (hxy : M.par x ≠ M.par y) : w = x ∨ w = y := by
  rcases M.isPar_three hx hy hw with rfl | rfl | rfl
  · exact (hxy rfl).elim
  · exact .inl rfl
  · exact .inr rfl

private theorem par_tgt (x : D) : (M.par x).tgt = M.kind := by
  unfold par
  split_ifs
  · rfl
  · rw [Atom.tgt, conv_conv, kind, M.legal.tgt_eq_src]
  · rfl

end Move

/-! ### The triangle of a move -/

variable [NeZero L.length] {T : Tilings L} {S : Ann L D} (hS : Good T S)

namespace Move

variable (M : Move S)

include hS in
private theorem par_q : M.par M.q = M.b.conv := by
  by_cases h : M.q = M.p
  · rw [h, par_p, M.legal.eq_conv_of_isUnit ((hS.isUnit_iff _ _).mpr h.symm), conv_conv]
  · simp [par, h]

include hS in
private theorem par_src (x : D) : (M.par x).src = (S.lab x x).src := by
  unfold par
  split_ifs with hp hq
  · rw [hp, M.legal.src_eq_src, hS.typed.src_eq]
  · rw [hq, ← Atom.tgt, M.legal.tgt_eq_tgt, hS.typed.tgt_eq]
  · rfl

include hS in
private theorem par_not_isUnit (x : D) : ¬(M.par x).IsUnit := by
  unfold par
  split_ifs with hp hq
  · intro ha
    refine M.fresh M.p ?_ (M.legal.eq_of_isUnit_left ha)
    rw [ha.eq_unit, M.legal.src_eq_src, hS.typed.src_eq]
    exact ((hS.isUnit_iff _ _).mpr rfl).eq_unit
  · intro hb
    rw [isUnit_conv] at hb
    refine M.fresh M.q (M.legal.eq_of_isUnit_right hb) ?_
    have h₁ : M.b.src = M.b.tgt := by rw [hb.eq_unit]; rfl
    rw [hb.eq_unit, h₁, M.legal.tgt_eq_tgt, hS.typed.tgt_eq]
    exact ((hS.isUnit_iff _ _).mpr rfl).eq_unit
  · exact id

/-- The labelling of the old nodes and the new node `none` before ∃ labels the edges that ∀ left
unlabelled. -/
private noncomputable def preLab : Option D → Option D → Atom (Fin L.length)
  | some x, some y => S.lab x y
  | some x, none => M.par x
  | none, some y => (M.par y).conv
  | none, none => unit M.kind

include hS in
private theorem typed_preLab : Typed M.preLab where
  src_eq x y := by
    rcases x with _ | x <;> rcases y with _ | y
    · rfl
    · exact M.par_tgt y
    · exact M.par_src hS x
    · exact hS.typed.src_eq x y
  conv_lab x y := by
    rcases x with _ | x <;> rcases y with _ | y
    · rfl
    · exact conv_conv _
    · rfl
    · exact hS.typed.conv_lab x y

include hS in
/-- The triangle of ∀'s move, on the two nodes he picked and the new node, is consistent. -/
private theorem tri_free {x y w : Option D} (hx : x = none ∨ x = some M.p ∨ x = some M.q)
    (hy : y = none ∨ y = some M.p ∨ y = some M.q) (hw : w = none ∨ w = some M.p ∨ w = some M.q) :
    ¬Rule L (M.preLab x y) (M.preLab y w) (M.preLab x w) := by
  intro hR
  obtain ⟨h₁, h₂, h₃⟩ := hR.not_isUnit
  have hunit (z : Option D) : (M.preLab z z).IsUnit := by
    rcases z with _ | z
    · trivial
    · exact (hS.isUnit_iff z z).mpr rfl
  have hxy : x ≠ y := fun h => h₁ (h ▸ hunit x)
  have hyw : y ≠ w := fun h => h₂ (h ▸ hunit y)
  have hxw : x ≠ w := fun h => h₃ (h ▸ hunit x)
  have hf := M.legal.not_forbidden
  have hq := M.par_q hS
  have hc := hS.typed.conv_lab M.p M.q
  simp only [Forbidden, not_or] at hf
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl <;>
    first
    | exact hxy rfl
    | exact hyw rfl
    | exact hxw rfl
    | simp only [preLab, par_p, hq, conv_conv, ← hc] at hR
      first
      | exact hf.1 hR
      | exact hf.2.1 hR
      | exact hf.2.2.1 hR
      | exact hf.2.2.2.1 hR
      | exact hf.2.2.2.2.1 hR
      | exact hf.2.2.2.2.2 hR

/-! ### The labels chosen by ∃ -/

open Classical in
/-- The node picked by ∀ that is joined to the new node by a step, when `h` sees it. -/
private noncomputable def stepPar (h : D) : Option D :=
  if hs : ∃ s, (∃ d, S.lab h s = green d .forward) ∧ (M.par s).IsStep then some hs.choose else none

omit [NeZero L.length] in
private theorem stepPar_spec {h s : D} (hs : M.stepPar h = some s) :
    (∃ d, S.lab h s = green d .forward) ∧ (M.par s).IsStep := by
  unfold stepPar at hs
  split_ifs at hs with h'
  obtain rfl := Option.some.inj hs
  exact h'.choose_spec

omit [NeZero L.length] in
private theorem stepPar_eq {h s : D} {d e : Axis} (hh : M.par h = green e .forward)
    (hs : S.lab h s = green d .forward) (hstep : (M.par s).IsStep) : M.stepPar h = some s := by
  have h' : ∃ s, (∃ d, S.lab h s = green d .forward) ∧ (M.par s).IsStep := ⟨s, ⟨d, hs⟩, hstep⟩
  simp only [stepPar, h', ↓reduceDIte, Option.some.injEq]
  have hne : M.par h ≠ M.par s := fun h => by simp [← h, hh, Atom.IsStep] at hstep
  have hc := h'.choose_spec.2
  rcases M.eq_of_isPar (M.isPar_of_green hh) (M.isPar_of_isStep hstep)
    (M.isPar_of_isStep hc) hne with h₁ | h₁
  · rw [h₁, hh] at hc
    simp [Atom.IsStep] at hc
  · exact h₁

open Classical in
/-- The classes after the move. The new node joins the class of the node to which a step joins
it, or starts a class; when the new node is a `0`-node, the nodes it sees are those picked by ∀,
and they form one class when a step joins them. -/
private noncomputable def newRoot : Option D → Option D → Option D
  | some h, some a => some (S.root h a)
  | some h, none => (M.stepPar h).map (S.root h)
  | none, some a => if (S.lab M.p a).IsStep then some M.p else some a
  | none, none => none

/-- The places in the classes after the move. -/
private noncomputable def newPot : Option D → Option D → ℤ
  | some h, some a => S.pot h a
  | some h, none => (M.stepPar h).elim 0 fun s => S.pot h s + (M.par s).sgn
  | none, some a => (S.lab M.p a).sgn
  | none, none => 0

/-- The new node and `x` are seen along green edges by one old node, so that the edge between
them must be a tile edge. -/
private def Apex (x : D) : Prop :=
  ∃ h d, S.lab h x = green d .forward ∧ M.par h = green d.other .forward

/-- The edges that are tile edges once ∃ has answered the move: the old ones, those that ∀ has
labelled with a tile atom and those between two nodes seen by one node. -/
private def WillTile : Option D → Option D → Prop
  | some x, some y => (S.lab x y).IsTile
  | some x, none => (M.par x).IsTile ∨ M.Apex x
  | none, _ => False

/-- The node `s` picked by ∀ constrains the edge from `x₀`, a node of axis `d`, to the new node
to lie at the cell `m`: either ∀ has labelled the edge from `s` with a tile atom, and `s` is `x₀`
or one step away from it, or he has labelled it with a step, and a tile edge joins `x₀` to `s`. -/
private def AnchorAt (d : Axis) (x₀ : D) (m : Cell L) (s : D) : Prop :=
  (∃ j o, M.par s = tile j o ∧ (x₀ = s ∨ (S.lab s x₀).IsStep) ∧
      m = ⟨j, (S.lab s x₀).sgn • d.vec⟩) ∨
    ((M.par s).IsStep ∧ (S.lab x₀ s).IsTile ∧
      m = ⟨(S.cell x₀ s).seed, (S.cell x₀ s).pos + (M.par s).sgn • d.other.vec⟩)

/-- The edge from `x₀`, a node of axis `d`, to the new node is constrained to lie at the cell
`m`. -/
private def Anchor (d : Axis) (x₀ : D) (m : Cell L) : Prop :=
  ∃ s, M.AnchorAt d x₀ m s

/-- The edge from `x` to the new node is constrained to lie at the cell `m`, by a constraint on a
node of the class of `x` under a node that sees the new node. -/
private def Cand (x : D) (m : Cell L) : Prop :=
  ∃ h x₀ e d m₀, M.par h = green e .forward ∧ S.lab h x = green d .forward ∧
    S.lab h x₀ = green d .forward ∧ S.root h x = S.root h x₀ ∧ M.Anchor d x₀ m₀ ∧
    m = ⟨m₀.seed, m₀.pos + (S.pot h x - S.pot h x₀) • d.vec⟩

open Classical in
/-- The cell of the edge from `x` to the new node: a cell to which it is constrained, and
otherwise a cell of the constant tiling. -/
private noncomputable def candCell (x : D) : Cell L :=
  if hc : ∃ m, M.Cand x m then hc.choose else ⟨0, 0⟩

/-- The cell of the edge from `x` to the new node: the origin of the tiling of the tile when ∀
has labelled the edge with a tile atom. -/
private noncomputable def cellAt (x : D) : Cell L :=
  match M.par x with
  | tile j _ => ⟨j, 0⟩
  | _ => M.candCell x

open Classical in
/-- The atom that ∃ puts on an edge from a `0`-node to a node of axis `d`. -/
private noncomputable def apexLabel (d : Axis) (U V : Prop) : Atom (Fin L.length) :=
  if U then u d .forward else if V then v d .forward else white .zero d.kind

/-- The axis of a kind of node other than `0`. -/
private def _root_.Cslib.RelationAlgebra.Tiling.Kind.axis : Kind → Option Axis
  | .zero => none
  | .one => some .one
  | .two => some .two

open Classical in
variable (T) in
/-- The atom that ∃ puts on the edge from `x` to the new node, when ∀ has not labelled it. -/
private noncomputable def exLabel (x : D) : Atom (Fin L.length) :=
  match (S.lab x x).src.axis, M.kind.axis with
  | none, none => white .zero .zero
  | none, some e => apexLabel e (UCond M.preLab M.newRoot e (some x) none)
      (VCond M.preLab M.newRoot M.WillTile e.other (some x) none)
  | some d, none => (apexLabel d (UCond M.preLab M.newRoot d none (some x))
      (VCond M.preLab M.newRoot M.WillTile d.other none (some x))).conv
  | some d, some e =>
    if d = e then white d.kind d.kind
    else if M.Apex x then tile (T.idx (M.candCell x)) d.tileDir else white d.kind e.kind

open Classical in
variable (T) in
/-- The atom on the edge from `x` to the new node. -/
private noncomputable def ext (x : D) : Atom (Fin L.length) :=
  if M.IsPar x then M.par x else M.exLabel T x

variable (T) in
/-- The labelling with which ∃ answers a move, on the old nodes and one new node `none`. -/
private noncomputable def next : Ann L (Option D) where
  lab
    | some x, some y => S.lab x y
    | some x, none => M.ext T x
    | none, some y => (M.ext T y).conv
    | none, none => unit M.kind
  root := M.newRoot
  pot := M.newPot
  cell
    | some x, some y => S.cell x y
    | some x, none => M.cellAt x
    | none, some y => M.cellAt y
    | none, none => ⟨0, 0⟩

@[simp]
private theorem _root_.Cslib.RelationAlgebra.Tiling.Kind.axis_eq_none {k : Kind} :
    k.axis = none ↔ k = .zero := by
  cases k <;> simp [Kind.axis]

@[simp]
private theorem _root_.Cslib.RelationAlgebra.Tiling.Kind.axis_eq_some {k : Kind} {d : Axis} :
    k.axis = some d ↔ k = d.kind := by
  cases k <;> cases d <;> simp [Kind.axis, Axis.kind]

/-- The atoms that ∃ may put on an edge to the new node, with the reason for each. -/
private theorem exLabel_cases (x : D) :
    (∃ i j, M.exLabel T x = white i j) ∨
    (∃ e, M.exLabel T x = u e .forward ∧ UCond M.preLab M.newRoot e (some x) none) ∨
    (∃ e, M.exLabel T x = v e .forward ∧
      VCond M.preLab M.newRoot M.WillTile e.other (some x) none) ∨
    (∃ d, M.exLabel T x = u d .reverse ∧ UCond M.preLab M.newRoot d none (some x)) ∨
    (∃ d, M.exLabel T x = v d .reverse ∧
      VCond M.preLab M.newRoot M.WillTile d.other none (some x)) ∨
    (∃ d : Axis, M.exLabel T x = tile (T.idx (M.candCell x)) d.tileDir ∧ M.Apex x) := by
  unfold exLabel
  split
  · exact .inl ⟨_, _, rfl⟩
  · unfold apexLabel
    split_ifs with hU hV
    · exact .inr (.inl ⟨_, rfl, hU⟩)
    · exact .inr (.inr (.inl ⟨_, rfl, hV⟩))
    · exact .inl ⟨_, _, rfl⟩
  · unfold apexLabel
    split_ifs with hU hV
    · exact .inr (.inr (.inr (.inl ⟨_, rfl, hU⟩)))
    · exact .inr (.inr (.inr (.inr (.inl ⟨_, rfl, hV⟩))))
    · exact .inl ⟨_, _, rfl⟩
  · split_ifs with hde hA
    · exact .inl ⟨_, _, rfl⟩
    · exact .inr (.inr (.inr (.inr (.inr ⟨_, rfl, hA⟩))))
    · exact .inl ⟨_, _, rfl⟩

private theorem exLabel_src (x : D) : (M.exLabel T x).src = (S.lab x x).src := by
  unfold exLabel
  split <;> rename_i hx hk
  · rw [Kind.axis_eq_none] at hx
    simp [hx]
  · rw [Kind.axis_eq_none] at hx
    unfold apexLabel
    split_ifs <;> simp [hx]
  · rw [Kind.axis_eq_some] at hx
    unfold apexLabel
    split_ifs <;> simp [hx, Atom.conv, Direction.flip]
  · rw [Kind.axis_eq_some] at hx
    split_ifs <;> simp [hx]

private theorem exLabel_tgt (x : D) : (M.exLabel T x).tgt = M.kind := by
  unfold exLabel
  split <;> rename_i hx hk
  · rw [Kind.axis_eq_none] at hk
    simp [hk]
  · rw [Kind.axis_eq_some] at hk
    unfold apexLabel
    split_ifs <;> simp [hk]
  · rw [Kind.axis_eq_none] at hk
    unfold apexLabel
    split_ifs <;> simp [hk, Atom.conv, Direction.flip, Atom.tgt]
  · rw [Kind.axis_eq_some] at hk
    rename_i d e
    split_ifs with hde <;> cases d <;> cases e <;> simp_all [Axis.other]

private theorem ext_of_isPar {x : D} (h : M.IsPar x) : M.ext T x = M.par x := by simp [ext, h]

private theorem ext_of_not_isPar {x : D} (h : ¬M.IsPar x) : M.ext T x = M.exLabel T x := by
  simp [ext, h]

include hS in
private theorem ext_src (x : D) : (M.ext T x).src = (S.lab x x).src := by
  by_cases h : M.IsPar x
  · rw [M.ext_of_isPar h, M.par_src hS]
  · rw [M.ext_of_not_isPar h, exLabel_src]

private theorem ext_tgt (x : D) : (M.ext T x).tgt = M.kind := by
  by_cases h : M.IsPar x
  · rw [M.ext_of_isPar h, par_tgt]
  · rw [M.ext_of_not_isPar h, exLabel_tgt]

include hS in
private theorem ext_not_isUnit (x : D) : ¬(M.ext T x).IsUnit := by
  by_cases h : M.IsPar x
  · rw [M.ext_of_isPar h]
    exact M.par_not_isUnit hS x
  · rw [M.ext_of_not_isPar h]
    obtain ⟨_, _, h⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ :=
      M.exLabel_cases (T := T) x <;> simp [h, Atom.IsUnit]

/-- ∃ puts no green atom on an edge. -/
private theorem par_of_ext_green {x : D} {d : Axis} {o : Direction} (h : M.ext T x = green d o) :
    M.par x = green d o := by
  by_cases hx : M.IsPar x
  · rwa [M.ext_of_isPar hx] at h
  · rw [M.ext_of_not_isPar hx] at h
    obtain ⟨_, _, h'⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ :=
      M.exLabel_cases (T := T) x <;> simp [h'] at h

/-- ∃ puts no step on an edge. -/
private theorem par_of_ext_isStep {x : D} (h : (M.ext T x).IsStep) :
    M.ext T x = M.par x ∧ M.IsPar x := by
  by_cases hx : M.IsPar x
  · exact ⟨M.ext_of_isPar hx, hx⟩
  · rw [M.ext_of_not_isPar hx] at h
    obtain ⟨_, _, h'⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ :=
      M.exLabel_cases (T := T) x <;> simp [h', Atom.IsStep] at h

private theorem par_of_ext_step {x : D} {d : Axis} {o : Direction} (h : M.ext T x = step d o) :
    M.par x = step d o :=
  (M.par_of_ext_isStep (T := T) (x := x) (by simp [h, Atom.IsStep])).1 ▸ h

/-- ∃ puts a tile atom only on an edge between two nodes seen by one node, and then the tile at
the cell chosen for the edge. -/
private theorem ext_tile {x : D} {i : Fin L.length} {o : Direction} (h : M.ext T x = tile i o) :
    M.par x = tile i o ∨ ¬M.IsPar x ∧ M.Apex x ∧ i = T.idx (M.candCell x) := by
  by_cases hx : M.IsPar x
  · rw [M.ext_of_isPar hx] at h
    exact .inl h
  · rw [M.ext_of_not_isPar hx] at h
    obtain ⟨_, _, h'⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', hA⟩ :=
      M.exLabel_cases (T := T) x <;> simp only [h', reduceCtorEq, tile.injEq] at h
    exact .inr ⟨hx, hA, h.1.symm⟩

@[simp]
private theorem next_lab_some (x y : D) : (M.next T).lab (some x) (some y) = S.lab x y := rfl

private theorem next_lab_p : (M.next T).lab (some M.p) none = M.a := by
  simp [next, M.ext_of_isPar (T := T) (.inl rfl), par_p]

include hS in
private theorem next_lab_q : (M.next T).lab none (some M.q) = M.b := by
  simp [next, M.ext_of_isPar (T := T) (.inr rfl), M.par_q hS]

/-! ### The cells of the new tile edges -/

omit [NeZero L.length] in
/-- A constraint on the cell of a new edge comes from a node picked by ∀ whose edge to the new
node he labelled with a tile atom or a step. -/
private theorem isPar_of_anchorAt {d : Axis} {x₀ s : D} {m : Cell L}
    (h : M.AnchorAt d x₀ m s) : M.IsPar s ∧ ((M.par s).IsTile ∨ (M.par s).IsStep) := by
  obtain ⟨j, o, hs, -⟩ | ⟨hs, -⟩ := h
  · have hs' : (M.par s).IsTile := by simp [hs, Atom.IsTile]
    exact ⟨M.isPar_of_isTile hs', .inl hs'⟩
  · exact ⟨M.isPar_of_isStep hs, .inr hs⟩

omit [NeZero L.length] in
private theorem exists_par_of_anchor {d : Axis} {x₀ : D} {m : Cell L} (h : M.Anchor d x₀ m) :
    ∃ s, M.IsPar s ∧ ((M.par s).IsTile ∨ (M.par s).IsStep) :=
  let ⟨s, hs⟩ := h
  ⟨s, M.isPar_of_anchorAt hs⟩

omit [NeZero L.length] in
/-- When ∀ has labelled an edge to the new node with a tile atom or a step, at most one node sees
the new node along a green edge. -/
private theorem green_par_unique {s h h' : D} {e e' : Axis} {o o' : Direction} (hs : M.IsPar s)
    (hs' : (M.par s).IsTile ∨ (M.par s).IsStep) (hh : M.par h = green e o)
    (hh' : M.par h' = green e' o') : h = h' := by
  have hne : M.par s ≠ M.par h := fun heq => by simp [heq, hh, Atom.IsTile, Atom.IsStep] at hs'
  rcases M.eq_of_isPar hs (M.isPar_of_green hh) (M.isPar_of_green hh') hne with h₁ | h₁
  · simp [← h₁, hh', Atom.IsTile, Atom.IsStep] at hs'
  · exact h₁.symm

include hS in
/-- The triangle of ∀'s move is consistent when read from one of the nodes he picked, through the
other, to the new node. -/
private theorem not_rule_par {s h : D} (hs : M.IsPar s) (hh : M.IsPar h) :
    ¬Rule L (S.lab s h) (M.par h) (M.par s) :=
  M.tri_free hS (x := some s) (y := some h) (w := none) (.inr (hs.imp (congrArg _) (congrArg _)))
    (.inr (hh.imp (congrArg _) (congrArg _))) (.inl rfl)

include hS in
/-- By rule 3, ∀ cannot pick a `0`-node and a node that it sees along `u`, and ask for a green
edge from the first and a tile other than `T₀` from the second. -/
private theorem par_tile_eq_zero {h s : D} {d e : Axis} {j : Fin L.length} {o : Direction}
    (hu : S.lab h s = u d .forward) (hh : M.par h = green e .forward) (hs : M.par s = tile j o) :
    j = 0 := by
  by_contra hj
  obtain ⟨d', rfl⟩ := o.exists_tileDir
  have hκ : (S.lab s s).src = d.kind := hS.typed.tgt_of_eq hu
  have h₁ : d'.kind = d.kind := by rw [← hκ, ← M.par_src hS s, hs, Atom.src_tile]
  have h₂ : d'.other.kind = M.kind := by rw [← M.par_tgt s, hs, Atom.tgt_tile]
  have h₃ : e.kind = M.kind := by rw [← M.par_tgt h, hh, Atom.tgt_green_forward]
  obtain rfl := Axis.kind_inj.mp h₁
  obtain rfl : e = d'.other := Axis.kind_inj.mp (h₃.trans h₂.symm)
  refine M.not_rule_par hS (s := s) (M.isPar_of_isTile (by simp [hs, Atom.IsTile]))
    (M.isPar_of_green hh) ?_
  rw [hS.typed.eq_conv hu, hh, hs]
  exact rule_u fun h0 => hj (Fin.ext h0)

include hS in
/-- By rule 4, ∀ cannot pick a `0`-node and a node that it sees along `v`, and ask for a green
edge from the first and a step from the second. -/
private theorem not_isStep_par {h s : D} {d e : Axis} (hv : S.lab h s = v d .forward)
    (hh : M.par h = green e .forward) : ¬(M.par s).IsStep := by
  intro hs
  obtain ⟨e', o, hs'⟩ := Atom.isStep_iff.mp hs
  have hκ : (S.lab s s).src = d.kind := hS.typed.tgt_of_eq hv
  have h₁ : e'.kind = d.kind := by rw [← hκ, ← M.par_src hS s, hs', Atom.src_step]
  have h₂ : e'.kind = M.kind := by rw [← M.par_tgt s, hs', Atom.tgt_step]
  have h₃ : e.kind = M.kind := by rw [← M.par_tgt h, hh, Atom.tgt_green_forward]
  obtain rfl := Axis.kind_inj.mp h₁
  obtain rfl : e = e' := Axis.kind_inj.mp (h₃.trans h₂.symm)
  refine M.not_rule_par hS (M.isPar_of_isStep hs) (M.isPar_of_green hh) ?_
  rw [hS.typed.eq_conv hv, hh, hs']
  exact rule_v e o

include hS in
/-- The constraints on the cell of a new edge agree. -/
private theorem cand_unique {x : D} {m m' : Cell L} (hm : M.Cand x m) (hm' : M.Cand x m') :
    m.seed = m'.seed ∧ (m.seed ≠ 0 → m.pos = m'.pos) := by
  obtain ⟨h, x₀, e, d, m₀, hh, hx, hx₀, hr, hA, rfl⟩ := hm
  obtain ⟨h', x₁, e', d', m₁, hh', hx', hx₁, hr', hA', rfl⟩ := hm'
  obtain ⟨s₀, hs₀, hs₀'⟩ := M.exists_par_of_anchor hA
  obtain rfl := M.green_par_unique hs₀ hs₀' hh hh'
  obtain rfl : d = d' := by simpa [hx] using hx'
  have hroot : S.root h x₀ = S.root h x₁ := hr.symm.trans hr'
  obtain ⟨s, hA⟩ := hA
  obtain ⟨s', hA'⟩ := hA'
  have hs := M.isPar_of_anchorAt hA
  have hs' := M.isPar_of_anchorAt hA'
  obtain rfl : s = s' := by
    have hne : M.par h ≠ M.par s := fun heq => by
      simp [← heq, hh, Atom.IsTile, Atom.IsStep] at hs
    rcases M.eq_of_isPar (M.isPar_of_green hh) hs.1 hs'.1 hne with h₁ | h₁
    · simp [h₁, hh, Atom.IsTile, Atom.IsStep] at hs'
    · exact h₁.symm
  rcases hA with ⟨j, o, hj, hnear, rfl⟩ | ⟨hstep, htile, rfl⟩ <;>
    rcases hA' with ⟨j', o', hj', hnear', rfl⟩ | ⟨hstep', htile', rfl⟩
  · obtain ⟨rfl, rfl⟩ : j = j' ∧ o = o' := by simpa [hj] using hj'
    refine ⟨rfl, fun hj0 => ?_⟩
    have key : S.pot h x₁ = S.pot h x₀ + ((S.lab s x₁).sgn - (S.lab s x₀).sgn) := by
      by_cases hsg : S.lab h s = green d .forward
      · have aux (y : D) (hy : S.lab h y = green d .forward)
            (hny : y = s ∨ (S.lab s y).IsStep) : S.pot h y = S.pot h s + (S.lab s y).sgn := by
          rcases hny with rfl | hstep
          · rw [((hS.isUnit_iff y y).mpr rfl).eq_unit]
            simp [Atom.sgn]
          · obtain ⟨e₁, o₁, hl⟩ := Atom.isStep_iff.mp hstep
            cases o₁
            · rw [hl, (hS.step_class hsg hy hl).2]
              simp [Atom.sgn]
            · rw [hl, (hS.step_class hy hsg (hS.typed.eq_conv hl)).2]
              simp [Atom.sgn]
        rw [aux x₀ hx₀ hnear, aux x₁ hx₁ hnear']
        ring
      · have h0 : (S.lab s x₀).IsStep := hnear.resolve_left fun h' => hsg (h' ▸ hx₀)
        have h1 : (S.lab s x₁).IsStep := hnear'.resolve_left fun h' => hsg (h' ▸ hx₁)
        by_cases hx01 : x₀ = x₁
        · subst hx01
          ring
        · have hU : UCond S.lab S.root d h s := ⟨x₀, x₁, ⟨hx01, hx₀, hx₁, hroot⟩,
            by rwa [← hS.typed.conv_lab, Atom.isStep_conv],
            by rwa [← hS.typed.conv_lab, Atom.isStep_conv]⟩
          rcases hS.u_class hU with hg | hu
          · exact (hsg hg).elim
          · exact (hj0 (M.par_tile_eq_zero hS hu hh hj)).elim
    simp only [key]
    module
  · simp [hj, Atom.IsStep] at hstep'
  · simp [hj', Atom.IsStep] at hstep
  · by_cases hx01 : x₀ = x₁
    · subst hx01
      exact ⟨rfl, fun _ => rfl⟩
    · have hV : VCond S.lab S.root (fun a y => (S.lab a y).IsTile) d h s :=
        ⟨x₀, x₁, ⟨hx01, hx₀, hx₁, hroot⟩, htile, htile'⟩
      rcases hS.v_class hV with hg | hv
      · obtain ⟨h₁, h₂⟩ := hS.cell_class hx₀ hx₁ hg hroot
        refine ⟨h₁.symm, fun h0 => ?_⟩
        simp only [h₂ h0]
        module
      · exact (M.not_isStep_par hS hv hh hstep).elim

include hS in
private theorem candCell_spec {x : D} {m : Cell L} (hm : M.Cand x m) :
    (M.candCell x).seed = m.seed ∧ (m.seed ≠ 0 → (M.candCell x).pos = m.pos) := by
  have hc : ∃ m, M.Cand x m := ⟨m, hm⟩
  obtain ⟨h₁, h₂⟩ := M.cand_unique hS hm hc.choose_spec
  simp only [candCell, hc, ↓reduceDIte]
  exact ⟨h₁.symm, fun h0 => (h₂ h0).symm⟩

private theorem candCell_of_not {x : D} (hm : ¬∃ m, M.Cand x m) :
    M.candCell x = ⟨0, 0⟩ := by
  simp [candCell, hm]

omit [NeZero L.length] in
private theorem exists_par_of_cand {x : D} {m : Cell L} (hm : M.Cand x m) :
    ∃ s, M.IsPar s ∧ ((M.par s).IsTile ∨ (M.par s).IsStep) := by
  obtain ⟨h, x₀, e, d, m₀, -, -, -, -, hA, -⟩ := hm
  exact M.exists_par_of_anchor hA

omit [NeZero L.length] in
/-- A constraint on the cell of a new edge gives one on the edges from the nodes of the same
class. -/
private theorem cand_of_class {h x x' : D} {d e : Axis} {m : Cell L} (hm : M.Cand x m)
    (hh : M.par h = green e .forward) (hx : S.lab h x = green d .forward)
    (hx' : S.lab h x' = green d .forward) (hr : S.root h x = S.root h x') :
    M.Cand x' ⟨m.seed, m.pos + (S.pot h x' - S.pot h x) • d.vec⟩ := by
  obtain ⟨h₀, x₀, e₀, d₀, m₀, hh₀, hx₀x, hx₀, hr₀, hA, rfl⟩ := hm
  obtain ⟨s, hs, hs'⟩ := M.exists_par_of_anchor hA
  obtain rfl := M.green_par_unique hs hs' hh₀ hh
  obtain rfl : d₀ = d := by simpa [hx₀x] using hx
  refine ⟨h₀, x₀, e, d₀, m₀, hh, hx', hx₀, hr.symm.trans hr₀, hA, ?_⟩
  simp only [Cell.mk.injEq, true_and]
  module

include hS in
/-- An edge that ∀ has labelled with a tile atom is constrained to the origin of the tiling of
its tile, when a node sees its ends. -/
private theorem cand_self {h x : D} {e d : Axis} {j : Fin L.length} {o : Direction}
    (hh : M.par h = green e .forward) (hx : S.lab h x = green d .forward)
    (hp : M.par x = tile j o) : M.Cand x ⟨j, 0⟩ :=
  ⟨h, x, e, d, ⟨j, (S.lab x x).sgn • d.vec⟩, hh, hx, hx, rfl,
    ⟨x, .inl ⟨j, o, hp, .inl rfl, rfl⟩⟩, by simp [hS.sgn_self]⟩

include hS in
private theorem cellAt_spec {x : D} {m : Cell L} (hm : M.Cand x m) :
    (M.cellAt x).seed = m.seed ∧ (m.seed ≠ 0 → (M.cellAt x).pos = m.pos) := by
  unfold cellAt
  split
  · rename_i j o hj
    obtain ⟨h, x₀, e, d, m₀, hh, hx, -, -, -, -⟩ := id hm
    obtain ⟨h₁, h₂⟩ := M.cand_unique hS (M.cand_self hS hh hx hj) hm
    exact ⟨h₁, fun h0 => h₂ (h₁ ▸ h0)⟩
  · exact M.candCell_spec hS hm

private theorem cellAt_of_not_isPar {x : D} (hx : ¬M.IsPar x) : M.cellAt x = M.candCell x := by
  simp [cellAt, M.par_of_not_isPar hx]

private theorem cellAt_of_not {x : D} (hm : ¬∃ m, M.Cand x m) (hx : ¬(M.par x).IsTile) :
    M.cellAt x = ⟨0, 0⟩ := by
  unfold cellAt
  split
  · rename_i j o hj
    simp [hj, Atom.IsTile] at hx
  · exact M.candCell_of_not hm

private theorem tile_idx_ext {x : D} {i : Fin L.length} {o : Direction}
    (h : M.ext T x = tile i o) : i = T.idx (M.cellAt x) := by
  rcases M.ext_tile h with hp | ⟨hx, -, hi⟩
  · simp [cellAt, hp, Tilings.idx, T.til_origin]
  · rw [hi, M.cellAt_of_not_isPar hx]

private theorem exists_cand_of_ne_zero {x : D} (hx : ¬M.IsPar x)
    (h : T.idx (M.cellAt x) ≠ 0) : ∃ m, M.Cand x m := by
  by_contra hm
  simp [M.cellAt_of_not hm fun ht => hx (M.isPar_of_isTile ht), Tilings.idx, T.til_zero] at h

include hS in
/-- ∃ puts a tile atom on an edge between two nodes seen by one node. -/
private theorem ext_of_apex {h x : D} {d : Axis} (hx : S.lab h x = green d .forward)
    (hh : M.par h = green d.other .forward) (hnp : ¬M.IsPar x) :
    M.ext T x = tile (T.idx (M.candCell x)) d.tileDir := by
  have h₁ : (S.lab x x).src.axis = some d := Kind.axis_eq_some.mpr (hS.typed.tgt_of_eq hx)
  have h₂ : M.kind.axis = some d.other :=
    Kind.axis_eq_some.mpr (by rw [← M.par_tgt h, hh, Atom.tgt_green_forward])
  have hA : M.Apex x := ⟨h, d, hx, hh⟩
  rw [M.ext_of_not_isPar hnp, exLabel]
  simp [h₁, h₂, hA]

include hS in
/-- The cell of a new tile edge from `y`, when the new node is one step away from a node joined
to `y` by a tile edge. -/
private theorem cellAt_of_step {s y : D} {e : Axis} {o : Direction} (hs : M.par s = step e o)
    (hys : (S.lab y s).IsTile) (hA : M.Apex y) :
    (M.cellAt y).seed = (S.cell y s).seed ∧ ((S.cell y s).seed ≠ 0 →
      (M.cellAt y).pos = (S.cell y s).pos + (M.par s).sgn • e.vec) := by
  obtain ⟨h, d, hy, hh⟩ := hA
  have h₁ : e.kind = M.kind := by rw [← M.par_tgt s, hs, Atom.tgt_step]
  have h₂ : d.other.kind = M.kind := by rw [← M.par_tgt h, hh, Atom.tgt_green_forward]
  obtain rfl : e = d.other := Axis.kind_inj.mp (h₁.trans h₂.symm)
  have hc : M.Cand y ⟨(S.cell y s).seed, (S.cell y s).pos + (M.par s).sgn • d.other.vec⟩ :=
    ⟨h, y, d.other, d, _, hh, hy, hy, rfl, ⟨s, .inr ⟨by simp [hs, Atom.IsStep], hys, rfl⟩⟩,
      by simp⟩
  exact M.cellAt_spec hS hc

include hS in
/-- The cell of a new tile edge from `x`, when ∀ has labelled with a tile atom the edge from a
node one step away from `x`. -/
private theorem cellAt_of_tile {s x : D} {j : Fin L.length} {o o' : Direction} {e : Axis}
    (hs : M.par s = tile j o) (hsx : S.lab s x = step e o') (hA : M.Apex x) :
    (M.cellAt x).seed = j ∧ (j ≠ 0 → (M.cellAt x).pos = (S.lab s x).sgn • e.vec) := by
  obtain ⟨h, d, hx, hh⟩ := hA
  have h₁ : (S.lab x x).src = d.kind := hS.typed.tgt_of_eq hx
  have h₂ : (S.lab x x).src = e.kind := by rw [hS.typed.tgt_of_eq hsx, Atom.tgt_step]
  obtain rfl : d = e := Axis.kind_inj.mp (h₁.symm.trans h₂)
  have hc : M.Cand x ⟨j, (S.lab s x).sgn • d.vec⟩ :=
    ⟨h, x, d.other, d, _, hh, hx, hx, rfl,
      ⟨s, .inl ⟨j, o, hs, .inr (by simp [hsx, Atom.IsStep]), rfl⟩⟩, by simp⟩
  exact M.cellAt_spec hS hc

include hS in
/-- The cells of the new tile edges from two nodes joined by a step are adjacent. -/
private theorem cellAt_of_apex {w x : D} {e : Axis} (hwx : S.lab w x = step e .forward)
    (hw : ¬M.IsPar w) (hx : ¬M.IsPar x) (hAw : M.Apex w) (hAx : M.Apex x) :
    (M.cellAt x).seed = (M.cellAt w).seed ∧
      ((M.cellAt w).seed ≠ 0 → (M.cellAt x).pos = (M.cellAt w).pos + e.vec) := by
  obtain ⟨hw₀, dw, hw', hhw⟩ := hAw
  obtain ⟨hx₀, dx, hx', hhx⟩ := hAx
  have h₁ : (S.lab w w).src = dw.kind := hS.typed.tgt_of_eq hw'
  have h₂ : (S.lab x x).src = dx.kind := hS.typed.tgt_of_eq hx'
  have h₃ : (S.lab w w).src = e.kind := hS.typed.src_of_eq hwx
  have h₄ : (S.lab x x).src = e.kind := by rw [hS.typed.tgt_of_eq hwx, Atom.tgt_step]
  obtain rfl : dw = e := Axis.kind_inj.mp (h₁.symm.trans h₃)
  obtain rfl : dx = dw := Axis.kind_inj.mp (h₂.symm.trans h₄)
  by_cases hc : (∃ m, M.Cand w m) ∨ ∃ m, M.Cand x m
  · obtain rfl : hw₀ = hx₀ := by
      obtain ⟨s, hs, hs'⟩ : ∃ s, M.IsPar s ∧ ((M.par s).IsTile ∨ (M.par s).IsStep) := by
        rcases hc with ⟨m, hm⟩ | ⟨m, hm⟩ <;> exact M.exists_par_of_cand hm
      exact M.green_par_unique hs hs' hhw hhx
    obtain ⟨hr, hp⟩ := hS.step_class hw' hx' hwx
    obtain ⟨m, hm⟩ : ∃ m, M.Cand w m := by
      rcases hc with hc | ⟨m, hm⟩
      · exact hc
      · exact ⟨_, M.cand_of_class hm hhw hx' hw' hr.symm⟩
    obtain ⟨a₁, a₂⟩ := M.cellAt_spec hS hm
    obtain ⟨b₁, b₂⟩ := M.cellAt_spec hS (M.cand_of_class hm hhw hw' hx' hr)
    refine ⟨b₁.trans a₁.symm, fun h0 => ?_⟩
    rw [a₁] at h0
    rw [b₂ h0, a₂ h0, hp]
    module
  · rw [not_or] at hc
    rw [M.cellAt_of_not hc.1 fun ht => hw (M.isPar_of_isTile ht),
      M.cellAt_of_not hc.2 fun ht => hx (M.isPar_of_isTile ht)]
    exact ⟨rfl, fun h0 => (h0 rfl).elim⟩

/-! ### The response is consistent -/

@[simp]
private theorem next_lab_some_none (x : D) : (M.next T).lab (some x) none = M.ext T x := rfl

@[simp]
private theorem next_lab_none_some (y : D) :
    (M.next T).lab none (some y) = (M.ext T y).conv := rfl

@[simp]
private theorem next_lab_none_none : (M.next T).lab none none = unit M.kind := rfl

include hS in
private theorem typed_next : Typed (M.next T).lab where
  src_eq x y := by
    rcases x with _ | x <;> rcases y with _ | y
    · rfl
    · exact M.ext_tgt y
    · exact M.ext_src hS x
    · exact hS.typed.src_eq x y
  conv_lab x y := by
    rcases x with _ | x <;> rcases y with _ | y
    · rfl
    · exact conv_conv _
    · rfl
    · exact hS.typed.conv_lab x y

include hS in
private theorem isUnit_iff_next (x y : Option D) : ((M.next T).lab x y).IsUnit ↔ x = y := by
  rcases x with _ | x <;> rcases y with _ | y
  · simp
  · simp [M.ext_not_isUnit hS]
  · simp [M.ext_not_isUnit hS]
  · simp [next_lab_some, hS.isUnit_iff]

private theorem next_lab_eq_preLab {x y : Option D}
    (hx : x = none ∨ x = some M.p ∨ x = some M.q) (hy : y = none ∨ y = some M.p ∨ y = some M.q) :
    (M.next T).lab x y = M.preLab x y := by
  rcases x with _ | x <;> rcases y with _ | y
  · rfl
  · have hy' : M.IsPar y := by simpa [IsPar] using hy
    simp [preLab, M.ext_of_isPar hy']
  · have hx' : M.IsPar x := by simpa [IsPar] using hx
    simp [preLab, M.ext_of_isPar hx']
  · rfl

private theorem isPar_of_ext_green {x : D} {d : Axis} {o : Direction}
    (h : M.ext T x = green d o) : M.IsPar x :=
  M.isPar_of_green (M.par_of_ext_green h)

private theorem ucond_of_ext_u_forward {x : D} {d : Axis} (h : M.ext T x = u d .forward)
    (hx : ¬M.IsPar x) : UCond M.preLab M.newRoot d (some x) none := by
  rw [M.ext_of_not_isPar hx] at h
  obtain ⟨_, _, h'⟩ | ⟨_, h', hc⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ :=
    M.exLabel_cases (T := T) x <;> simp only [h', reduceCtorEq, u.injEq, and_true, and_false] at h
  exact h ▸ hc

private theorem ucond_of_ext_u_reverse {x : D} {d : Axis} (h : M.ext T x = u d .reverse)
    (hx : ¬M.IsPar x) : UCond M.preLab M.newRoot d none (some x) := by
  rw [M.ext_of_not_isPar hx] at h
  obtain ⟨_, _, h'⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', hc⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ :=
    M.exLabel_cases (T := T) x <;> simp only [h', reduceCtorEq, u.injEq, and_true, and_false] at h
  exact h ▸ hc

private theorem vcond_of_ext_v_forward {x : D} {d : Axis} (h : M.ext T x = v d .forward)
    (hx : ¬M.IsPar x) : VCond M.preLab M.newRoot M.WillTile d.other (some x) none := by
  rw [M.ext_of_not_isPar hx] at h
  obtain ⟨_, _, h'⟩ | ⟨_, h', -⟩ | ⟨_, h', hc⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ :=
    M.exLabel_cases (T := T) x <;> simp only [h', reduceCtorEq, v.injEq, and_true, and_false] at h
  exact h ▸ hc

private theorem vcond_of_ext_v_reverse {x : D} {d : Axis} (h : M.ext T x = v d .reverse)
    (hx : ¬M.IsPar x) : VCond M.preLab M.newRoot M.WillTile d.other none (some x) := by
  rw [M.ext_of_not_isPar hx] at h
  obtain ⟨_, _, h'⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', hc⟩ | ⟨_, h', -⟩ :=
    M.exLabel_cases (T := T) x <;> simp only [h', reduceCtorEq, v.injEq, and_true, and_false] at h
  exact h ▸ hc

/-! ### No new triangle is forbidden

Each lemma takes a triangle on the new node and two old nodes that are not both picked by ∀, and
excludes one of the four shapes of `Rule.cases`, for one place of the new node in the triangle. -/

include hS in
private theorem rule_one_left {y w : D} (hr : M.ext T y = green .one .forward)
    (hs : S.lab y w = green .two .forward) (ht : M.ext T w = white .two .one)
    (hnp : ¬(M.IsPar y ∧ M.IsPar w)) : False := by
  have hy := M.par_of_ext_green hr
  have hw : ¬M.IsPar w := fun hw => hnp ⟨M.isPar_of_green hy, hw⟩
  rw [M.ext_of_apex hS (d := .two) hs hy hw] at ht
  cases ht

include hS in
private theorem rule_one_right {x y : D} (hr : S.lab x y = green .one .reverse)
    (hs : M.ext T y = green .two .forward) (ht : M.ext T x = white .one .two)
    (hnp : ¬(M.IsPar x ∧ M.IsPar y)) : False := by
  have hy := M.par_of_ext_green hs
  have hx : ¬M.IsPar x := fun hx => hnp ⟨hx, M.isPar_of_green hy⟩
  rw [M.ext_of_apex hS (d := .one) (hS.typed.eq_conv hr) hy hx] at ht
  cases ht

include hS in
private theorem rule_two_mid {x w : D} {d : Axis} {i j : Fin L.length} {o o' : Direction}
    (hr : M.ext T x = tile i o) (hs : M.ext T w = tile j o') (ht : S.lab w x = step d .forward)
    (hnp : ¬(M.IsPar x ∧ M.IsPar w)) : d.front L[j] = d.back L[i] := by
  have hi := M.tile_idx_ext hr
  have hj := M.tile_idx_ext hs
  suffices h : (M.cellAt x).seed = (M.cellAt w).seed ∧
      ((M.cellAt w).seed ≠ 0 → (M.cellAt x).pos = (M.cellAt w).pos + d.vec) by
    subst hi hj
    exact T.front_eq_back h.1 h.2
  rcases M.ext_tile hr with hpx | ⟨hx, hAx, -⟩ <;> rcases M.ext_tile hs with hpw | ⟨hw, hAw, -⟩
  · exact (hnp ⟨M.isPar_of_isTile (by simp [hpx, Atom.IsTile]),
      M.isPar_of_isTile (by simp [hpw, Atom.IsTile])⟩).elim
  · have ht' : S.lab x w = step d .reverse := hS.typed.eq_conv ht
    obtain ⟨h₁, h₂⟩ := M.cellAt_of_tile hS hpx ht' hAw
    have hcx : M.cellAt x = ⟨i, 0⟩ := by simp [cellAt, hpx]
    refine ⟨by rw [hcx, h₁], fun h0 => ?_⟩
    rw [h₁] at h0
    rw [hcx, h₂ h0, ht']
    simp [Atom.sgn]
  · obtain ⟨h₁, h₂⟩ := M.cellAt_of_tile hS hpw ht hAx
    have hcw : M.cellAt w = ⟨j, 0⟩ := by simp [cellAt, hpw]
    refine ⟨by rw [hcw, h₁], fun h0 => ?_⟩
    rw [hcw] at h0
    rw [hcw, h₂ h0, ht]
    simp [Atom.sgn]
  · exact M.cellAt_of_apex hS ht hw hx hAw hAx

include hS in
private theorem rule_two_left {y w : D} {d : Axis} {i j : Fin L.length} {o o' : Direction}
    (hr : M.ext T y = tile i o) (hs : S.lab y w = tile j o') (ht : M.ext T w = step d .forward)
    (hnp : ¬(M.IsPar y ∧ M.IsPar w)) : d.front L[j] = d.back L[i] := by
  have hpw := M.par_of_ext_step ht
  have hy : ¬M.IsPar y := fun hy => hnp ⟨hy, M.isPar_of_isStep (by simp [hpw, Atom.IsStep])⟩
  rcases M.ext_tile hr with hp | ⟨-, hA, -⟩
  · exact (hy (M.isPar_of_isTile (by simp [hp, Atom.IsTile]))).elim
  obtain ⟨h₁, h₂⟩ := M.cellAt_of_step hS hpw (by simp [hs, Atom.IsTile]) hA
  have hi := M.tile_idx_ext hr
  have hj := hS.tile_idx hs
  subst hi hj
  refine T.front_eq_back h₁ fun h0 => ?_
  rw [h₂ h0, hpw]
  simp [Atom.sgn]

include hS in
private theorem rule_two_right {x y : D} {d : Axis} {i j : Fin L.length} {o o' : Direction}
    (hr : S.lab x y = tile i o) (hs : M.ext T y = tile j o') (ht : M.ext T x = step d .reverse)
    (hnp : ¬(M.IsPar x ∧ M.IsPar y)) : d.front L[j] = d.back L[i] := by
  have hpx := M.par_of_ext_step ht
  have hy : ¬M.IsPar y := fun hy => hnp ⟨M.isPar_of_isStep (by simp [hpx, Atom.IsStep]), hy⟩
  rcases M.ext_tile hs with hp | ⟨-, hA, -⟩
  · exact (hy (M.isPar_of_isTile (by simp [hp, Atom.IsTile]))).elim
  have hyx : (S.lab y x).IsTile := by
    rw [← hS.typed.conv_lab, hr]
    trivial
  obtain ⟨h₁, h₂⟩ := M.cellAt_of_step hS hpx hyx hA
  have hi := hS.tile_idx hr
  have hj := M.tile_idx_ext hs
  subst hi hj
  refine T.front_eq_back (by rw [hS.cell_symm x y, h₁]) fun h0 => ?_
  rw [hS.cell_symm x y, h₂ (h₁ ▸ h0), hpx]
  simp only [Atom.sgn]
  module

omit [NeZero L.length] in
/-- When two distinct nodes picked by ∀ carry the same atom, no third node carrying another atom
is picked. -/
private theorem not_isPar_of_twins {a a' w : D} (ha : M.IsPar a) (ha' : M.IsPar a')
    (hne : a ≠ a') (hw : M.par w ≠ M.par a) (hw' : M.par w ≠ M.par a') : ¬M.IsPar w := by
  intro hpw
  rcases M.isPar_three ha ha' hpw with h | h | h
  · exact hne h
  · exact hw (h ▸ rfl)
  · exact hw' (h ▸ rfl)

omit [NeZero L.length] in
/-- Two distinct nodes that the new node sees along green edges of one axis are the nodes picked
by ∀. -/
private theorem twin_none {a a' : Option D} {d : Axis} (hne : a ≠ a')
    (ha : M.preLab none a = green d .forward) (ha' : M.preLab none a' = green d .forward) :
    ∃ x x', a = some x ∧ a' = some x' ∧ x ≠ x' ∧ M.par x = green d .reverse ∧
      M.par x' = green d .reverse ∧ ∀ w, M.IsPar w → w = x ∨ w = x' := by
  rcases a with _ | x
  · cases ha
  rcases a' with _ | x'
  · cases ha'
  have hx : M.par x = green d .reverse := Atom.conv_eq_iff.mp ha
  have hx' : M.par x' = green d .reverse := Atom.conv_eq_iff.mp ha'
  have hxx : x ≠ x' := fun h => hne (congrArg _ h)
  refine ⟨x, x', rfl, rfl, hxx, hx, hx', fun w hw => ?_⟩
  rcases M.isPar_three (M.isPar_of_green hx) (M.isPar_of_green hx') hw with h | h | h
  · exact (hxx h).elim
  · exact .inl h.symm
  · exact .inr h.symm

private theorem rule_three_mid {x w : D} {d : Axis} (hr : M.ext T x = u d .reverse)
    (hs : M.ext T w = green d.other .reverse) (hnp : ¬(M.IsPar x ∧ M.IsPar w)) : False := by
  have hw := M.par_of_ext_green hs
  have hx : ¬M.IsPar x := fun hx => hnp ⟨hx, M.isPar_of_green hw⟩
  obtain ⟨a, a', ⟨hne, ha, ha', -⟩, -, -⟩ := M.ucond_of_ext_u_reverse hr hx
  obtain ⟨_, _, -, -, -, h₁, h₂, hall⟩ := M.twin_none hne ha ha'
  rcases hall w (M.isPar_of_green hw) with rfl | rfl
  · simp [hw] at h₁
  · simp [hw] at h₂

private theorem rule_three_left {y w : D} {d : Axis} {i : Fin L.length} {o : Direction}
    (hr : M.ext T y = u d .forward) (ht : M.ext T w = tile i o) (hi : i ≠ 0)
    (hnp : ¬(M.IsPar y ∧ M.IsPar w)) : False := by
  by_cases hy : M.IsPar y
  · have hw : ¬M.IsPar w := fun hw => hnp ⟨hy, hw⟩
    obtain ⟨m, hm⟩ := M.exists_cand_of_ne_zero hw (M.tile_idx_ext ht ▸ hi)
    obtain ⟨h, x₀, e, d', m₀, hh, -, -, -, hA, -⟩ := hm
    obtain ⟨s, hs, hs'⟩ := M.exists_par_of_anchor hA
    have hy' : M.par y = u d .forward := by rw [← M.ext_of_isPar (T := T) hy, hr]
    rcases M.isPar_three hy (M.isPar_of_green hh) hs with h₁ | h₁ | h₁
    · simp [h₁, hh] at hy'
    · simp [← h₁, hy', Atom.IsTile, Atom.IsStep] at hs'
    · simp [← h₁, hh, Atom.IsTile, Atom.IsStep] at hs'
  · obtain ⟨a, a', ⟨hne, -, -, -⟩, hst, hst'⟩ := M.ucond_of_ext_u_forward hr hy
    rcases a with _ | a
    · cases hst
    rcases a' with _ | a'
    · cases hst'
    have hst₁ : (M.par a).IsStep := hst
    have hst₂ : (M.par a').IsStep := hst'
    have hne' : a ≠ a' := fun h => hne (congrArg _ h)
    rcases M.ext_tile ht with hp | ⟨-, ⟨h, d', -, hh⟩, -⟩
    · refine M.not_isPar_of_twins (M.isPar_of_isStep hst₁) (M.isPar_of_isStep hst₂) hne' ?_ ?_
        (M.isPar_of_isTile (x := w) (by simp [hp, Atom.IsTile])) <;> intro h
      · simp [← h, hp, Atom.IsStep] at hst₁
      · simp [← h, hp, Atom.IsStep] at hst₂
    · refine M.not_isPar_of_twins (M.isPar_of_isStep hst₁) (M.isPar_of_isStep hst₂) hne' ?_ ?_
        (M.isPar_of_green hh) <;> intro h
      · simp [← h, hh, Atom.IsStep] at hst₁
      · simp [← h, hh, Atom.IsStep] at hst₂

include hS in
private theorem rule_three_right {x y : D} {d : Axis} {i : Fin L.length} {o : Direction}
    (hr : S.lab x y = u d .reverse) (hs : M.ext T y = green d.other .forward)
    (ht : M.ext T x = tile i o) (hi : i ≠ 0) (hnp : ¬(M.IsPar x ∧ M.IsPar y)) : False := by
  have hy := M.par_of_ext_green hs
  have hx : ¬M.IsPar x := fun hx => hnp ⟨hx, M.isPar_of_green hy⟩
  rcases M.ext_tile ht with hp | ⟨-, ⟨h, d', hx', hh⟩, -⟩
  · exact hx (M.isPar_of_isTile (by simp [hp, Atom.IsTile]))
  · obtain ⟨m, hm⟩ := M.exists_cand_of_ne_zero hx (M.tile_idx_ext ht ▸ hi)
    obtain ⟨s, hs₁, hs₂⟩ := M.exists_par_of_cand hm
    obtain rfl := M.green_par_unique hs₁ hs₂ hh hy
    have hu := hS.typed.eq_conv hr
    rw [hx'] at hu
    cases hu

private theorem rule_four_mid {x w : D} {d : Axis} (hr : M.ext T x = v d .reverse)
    (hs : M.ext T w = green d .reverse) (hnp : ¬(M.IsPar x ∧ M.IsPar w)) : False := by
  have hw := M.par_of_ext_green hs
  have hx : ¬M.IsPar x := fun hx => hnp ⟨hx, M.isPar_of_green hw⟩
  obtain ⟨a, a', ⟨hne, ha, ha', -⟩, -, -⟩ := M.vcond_of_ext_v_reverse hr hx
  obtain ⟨_, _, -, -, -, h₁, h₂, hall⟩ := M.twin_none hne ha ha'
  rcases hall w (M.isPar_of_green hw) with rfl | rfl
  · simp [hw] at h₁
  · simp [hw] at h₂

include hS in
private theorem rule_four_left {y w : D} {d : Axis} (hr : M.ext T y = v d .forward)
    (ht : (M.ext T w).IsStep) (hnp : ¬(M.IsPar y ∧ M.IsPar w)) : False := by
  obtain ⟨hw₁, hw⟩ := M.par_of_ext_isStep ht
  rw [hw₁] at ht
  have hy : ¬M.IsPar y := fun hy => hnp ⟨hy, hw⟩
  obtain ⟨a, a', ⟨hne, ha, ha', hroot⟩, hwt, hwt'⟩ := M.vcond_of_ext_v_forward hr hy
  rcases a with _ | t
  · cases hwt
  rcases a' with _ | t'
  · cases hwt'
  have hne' : t ≠ t' := fun h => hne (congrArg _ h)
  have key (t t' : D) (hne : t ≠ t') (ht₁ : M.WillTile (some t) none)
      (ht₂ : M.WillTile (some t') none) : M.Apex t := by
    refine ht₁.resolve_left fun hp => ?_
    have hpt := M.isPar_of_isTile hp
    have hwt : M.par w ≠ M.par t := fun h => by
      obtain ⟨_, _, h'⟩ := Atom.isStep_iff.mp ht
      simp [← h, h', Atom.IsTile] at hp
    rcases ht₂ with hp' | ⟨h, d', -, hh⟩
    · rcases M.eq_of_isPar hw hpt (M.isPar_of_isTile hp') hwt with h₁ | h₁
      · obtain ⟨_, _, h'⟩ := Atom.isStep_iff.mp ht
        simp [h₁, h', Atom.IsTile] at hp'
      · exact hne h₁.symm
    · rcases M.eq_of_isPar hw hpt (M.isPar_of_green hh) hwt with h₁ | h₁
      · subst h₁
        simp [hh, Atom.IsStep] at ht
      · subst h₁
        simp [hh, Atom.IsTile] at hp
  obtain ⟨h, d₁, ht₁, hh⟩ := key t t' hne' hwt hwt'
  obtain ⟨h', d₂, ht₂, hh'⟩ := key t' t hne'.symm hwt' hwt
  obtain rfl := M.green_par_unique hw (.inr ht) hh hh'
  have ha₁ : S.lab y t = green d.other .forward := ha
  have ha₂ : S.lab y t' = green d.other .forward := ha'
  obtain rfl : d₁ = d.other :=
    Axis.kind_inj.mp ((hS.typed.tgt_of_eq ht₁).symm.trans (hS.typed.tgt_of_eq ha₁))
  obtain rfl : d₂ = d.other :=
    Axis.kind_inj.mp ((hS.typed.tgt_of_eq ht₂).symm.trans (hS.typed.tgt_of_eq ha₂))
  obtain rfl := hS.apex_unique ⟨hne', ha₁, ha₂, Option.some.inj hroot⟩ ht₁ ht₂
  exact hy (M.isPar_of_green hh)

include hS in
private theorem rule_free_next (x y w : Option D) :
    ¬Rule L ((M.next T).lab x y) ((M.next T).lab y w) ((M.next T).lab x w) := by
  intro hR
  by_cases hT : (x = none ∨ x = some M.p ∨ x = some M.q) ∧
      (y = none ∨ y = some M.p ∨ y = some M.q) ∧ (w = none ∨ w = some M.p ∨ w = some M.q)
  · rw [M.next_lab_eq_preLab hT.1 hT.2.1, M.next_lab_eq_preLab hT.2.1 hT.2.2,
      M.next_lab_eq_preLab hT.1 hT.2.2] at hR
    exact M.tri_free hS hT.1 hT.2.1 hT.2.2 hR
  obtain ⟨h₁, h₂, h₃⟩ := hR.not_isUnit
  rcases x with _ | x <;> rcases y with _ | y <;> rcases w with _ | w
  · simp at h₁
  · simp at h₁
  · simp at h₃
  · have hnp : ¬(M.IsPar y ∧ M.IsPar w) := fun h => hT ⟨.inl rfl,
      .inr (h.1.imp (congrArg _) (congrArg _)), .inr (h.2.imp (congrArg _) (congrArg _))⟩
    simp only [next_lab_none_some, next_lab_some] at hR
    obtain ⟨hr, hs, ht⟩ | ⟨d, i, j, hr, hs, ht, hne⟩ | ⟨d, i, hr, hs, ht, hi⟩ |
      ⟨d, o, hr, hs, ht⟩ := hR.cases
    · exact M.rule_one_left hS (Atom.conv_eq_iff.mp hr) hs (Atom.conv_eq_iff.mp ht) hnp
    · exact hne (M.rule_two_left hS (Atom.conv_eq_iff.mp hr) hs (Atom.conv_eq_iff.mp ht)
        hnp).symm
    · exact M.rule_three_left (Atom.conv_eq_iff.mp hr) (Atom.conv_eq_iff.mp ht)
        (fun h => hi (by simp [h])) hnp
    · exact M.rule_four_left hS (Atom.conv_eq_iff.mp hr)
        (Atom.isStep_conv.mp (by simp [ht, Atom.IsStep])) hnp
  · simp at h₂
  · have hnp : ¬(M.IsPar x ∧ M.IsPar w) := fun h => hT ⟨
      .inr (h.1.imp (congrArg _) (congrArg _)), .inl rfl, .inr (h.2.imp (congrArg _) (congrArg _))⟩
    simp only [next_lab_none_some, next_lab_some, next_lab_some_none] at hR
    obtain ⟨hr, hs, ht⟩ | ⟨d, i, j, hr, hs, ht, hne⟩ | ⟨d, i, hr, hs, ht, hi⟩ |
      ⟨d, o, hr, hs, ht⟩ := hR.cases
    · exact hnp ⟨M.isPar_of_ext_green hr, M.isPar_of_ext_green (Atom.conv_eq_iff.mp hs)⟩
    · exact hne (M.rule_two_mid hS hr (Atom.conv_eq_iff.mp hs) (hS.typed.eq_conv ht) hnp).symm
    · exact M.rule_three_mid hr (Atom.conv_eq_iff.mp hs) hnp
    · exact M.rule_four_mid hr (Atom.conv_eq_iff.mp hs) hnp
  · have hnp : ¬(M.IsPar x ∧ M.IsPar y) := fun h => hT ⟨
      .inr (h.1.imp (congrArg _) (congrArg _)), .inr (h.2.imp (congrArg _) (congrArg _)), .inl rfl⟩
    simp only [next_lab_some, next_lab_some_none] at hR
    obtain ⟨hr, hs, ht⟩ | ⟨d, i, j, hr, hs, ht, hne⟩ | ⟨d, i, hr, hs, ht, hi⟩ |
      ⟨d, o, hr, hs, ht⟩ := hR.cases
    · exact M.rule_one_right hS hr hs ht hnp
    · exact hne (M.rule_two_right hS hr hs ht hnp).symm
    · exact M.rule_three_right hS hr hs ht (fun h => hi (by simp [h])) hnp
    · exact hnp ⟨(M.par_of_ext_isStep (T := T) (x := x) (by simp [ht, Atom.IsStep])).2,
        M.isPar_of_ext_green hs⟩
  · exact hS.rule_free x y w hR

/-! ### The response satisfies the invariant -/

omit [NeZero L.length] in
private theorem newRoot_step {h s : D} {d e : Axis} (hh : M.par h = green e .forward)
    (hs : S.lab h s = green d .forward) (hstep : (M.par s).IsStep) :
    M.newRoot (some h) none = some (S.root h s) ∧
      M.newPot (some h) none = S.pot h s + (M.par s).sgn := by
  simp [newRoot, newPot, M.stepPar_eq hh hs hstep]

include hS in
/-- When the new node lies in the class of an old node under `h`, a step joins it to a node
picked by ∀ that `h` sees. -/
private theorem exists_step_of_newRoot {h a : D} {d : Axis} (hh : M.par h = green d .forward)
    (hr : M.newRoot (some h) none = M.newRoot (some h) (some a)) :
    ∃ s o, S.lab h s = green d .forward ∧ M.par s = step d o ∧ S.root h s = S.root h a ∧
      M.newPot (some h) none = S.pot h s + (M.par s).sgn := by
  simp only [newRoot, Option.map_eq_some_iff] at hr
  obtain ⟨s, hs, hroot⟩ := hr
  obtain ⟨⟨d', hd⟩, hstep⟩ := M.stepPar_spec hs
  obtain ⟨e, o, he⟩ := Atom.isStep_iff.mp hstep
  have h₁ : (S.lab s s).src = e.kind := by rw [← M.par_src hS s, he, Atom.src_step]
  have h₂ : M.kind = e.kind := by rw [← M.par_tgt s, he, Atom.tgt_step]
  have h₃ : M.kind = d.kind := by rw [← M.par_tgt h, hh, Atom.tgt_green_forward]
  have h₄ : (S.lab s s).src = d'.kind := hS.typed.tgt_of_eq hd
  obtain rfl : d = e := Axis.kind_inj.mp (h₃.symm.trans h₂)
  obtain rfl : d = d' := Axis.kind_inj.mp (h₁.symm.trans h₄)
  exact ⟨s, o, hd, he, hroot, by simp [newPot, hs]⟩

include hS in
private theorem step_class_next {h a b : Option D} {d e : Axis}
    (ha : (M.next T).lab h a = green d .forward) (hb : (M.next T).lab h b = green d .forward)
    (hab : (M.next T).lab a b = step e .forward) :
    M.newRoot h a = M.newRoot h b ∧ M.newPot h b = M.newPot h a + 1 := by
  rcases h with _ | h
  · rcases a with _ | a
    · cases ha
    rcases b with _ | b
    · cases hb
    have ha' := M.isPar_of_ext_green (Atom.conv_eq_iff.mp ha)
    have hb' := M.isPar_of_ext_green (Atom.conv_eq_iff.mp hb)
    have hab' : S.lab a b = step e .forward := hab
    have hself : ¬(S.lab M.p M.p).IsStep := by
      rw [((hS.isUnit_iff M.p M.p).mpr rfl).eq_unit]
      exact id
    have hne : a ≠ b := fun h => by
      have h₁ := (hS.isUnit_iff a b).mpr h
      rw [hab'] at h₁
      exact h₁
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact (hne rfl).elim
    · have hpq : (S.lab M.p M.q).IsStep := by simp [hab', Atom.IsStep]
      have hsgn : (S.lab M.p M.q).sgn = 1 := by rw [hab']; rfl
      simp [newRoot, newPot, hpq, hself, hsgn, hS.sgn_self]
    · have h₁ : S.lab M.p M.q = step e .reverse := hS.typed.eq_conv hab'
      have hpq : (S.lab M.p M.q).IsStep := by simp [h₁, Atom.IsStep]
      have hsgn : (S.lab M.p M.q).sgn = -1 := by rw [h₁]; rfl
      simp [newRoot, newPot, hpq, hself, hsgn, hS.sgn_self]
    · exact (hne rfl).elim
  · rcases a with _ | a <;> rcases b with _ | b
    · cases hab
    · have hh := M.par_of_ext_green ha
      have hpb : M.par b = step e .reverse := M.par_of_ext_step (Atom.conv_eq_iff.mp hab)
      obtain ⟨h₁, h₂⟩ := M.newRoot_step hh hb (by simp [hpb, Atom.IsStep])
      refine ⟨h₁, ?_⟩
      rw [h₂, hpb]
      simp [newPot, Atom.sgn]
    · have hh := M.par_of_ext_green hb
      have hpa : M.par a = step e .forward := M.par_of_ext_step hab
      obtain ⟨h₁, h₂⟩ := M.newRoot_step hh ha (by simp [hpa, Atom.IsStep])
      refine ⟨h₁.symm, ?_⟩
      rw [h₂, hpa]
      simp [newPot, Atom.sgn]
    · obtain ⟨h₁, h₂⟩ := hS.step_class ha hb hab
      exact ⟨congrArg some h₁, h₂⟩

private theorem preLab_of_green {x y : Option D} {d : Axis} {o : Direction}
    (h : (M.next T).lab x y = green d o) : M.preLab x y = green d o := by
  rcases x with _ | x <;> rcases y with _ | y
  · exact h
  · have h' := M.par_of_ext_green (Atom.conv_eq_iff.mp h)
    change (M.par y).conv = green d o
    rw [h']
    exact conv_conv (green d o)
  · exact M.par_of_ext_green h
  · exact h

private theorem isStep_preLab {x y : Option D} (h : ((M.next T).lab x y).IsStep) :
    (M.preLab x y).IsStep := by
  rcases x with _ | x <;> rcases y with _ | y
  · exact h
  · have h' : (M.ext T y).IsStep := Atom.isStep_conv.mp h
    change (M.par y).conv.IsStep
    rw [Atom.isStep_conv, ← (M.par_of_ext_isStep h').1]
    exact h'
  · change (M.par x).IsStep
    rw [← (M.par_of_ext_isStep (T := T) (x := x) h).1]
    exact h
  · exact h

private theorem ucond_pre {h b : Option D} {d : Axis}
    (hU : UCond (M.next T).lab M.newRoot d h b) : UCond M.preLab M.newRoot d h b := by
  obtain ⟨a, a', ⟨hne, ha, ha', hr⟩, hs, hs'⟩ := hU
  exact ⟨a, a', ⟨hne, M.preLab_of_green ha, M.preLab_of_green ha', hr⟩, M.isStep_preLab hs,
    M.isStep_preLab hs'⟩

private theorem willTile_of_isTile {a : D} (h : (M.ext T a).IsTile) :
    M.WillTile (some a) none := by
  obtain ⟨i, o, hi⟩ := Atom.isTile_iff.mp h
  rcases M.ext_tile hi with hp | ⟨-, hA, -⟩
  · exact .inl (by simp [hp, Atom.IsTile])
  · exact .inr hA

private theorem exLabel_u_forward {x : D} {d : Axis} (hx : (S.lab x x).src = .zero)
    (hk : M.kind = d.kind) (hU : UCond M.preLab M.newRoot d (some x) none) :
    M.exLabel T x = u d .forward := by
  have h₁ : (S.lab x x).src.axis = none := Kind.axis_eq_none.mpr hx
  have h₂ : M.kind.axis = some d := Kind.axis_eq_some.mpr hk
  simp [exLabel, h₁, h₂, apexLabel, hU]

private theorem exLabel_v_forward {x : D} {d : Axis} (hx : (S.lab x x).src = .zero)
    (hk : M.kind = d.kind) (hU : ¬UCond M.preLab M.newRoot d (some x) none)
    (hV : VCond M.preLab M.newRoot M.WillTile d.other (some x) none) :
    M.exLabel T x = v d .forward := by
  have h₁ : (S.lab x x).src.axis = none := Kind.axis_eq_none.mpr hx
  have h₂ : M.kind.axis = some d := Kind.axis_eq_some.mpr hk
  simp [exLabel, h₁, h₂, apexLabel, hU, hV]

private theorem exLabel_u_reverse {x : D} {d : Axis} (hx : (S.lab x x).src = d.kind)
    (hk : M.kind = .zero) (hU : UCond M.preLab M.newRoot d none (some x)) :
    M.exLabel T x = u d .reverse := by
  have h₁ : (S.lab x x).src.axis = some d := Kind.axis_eq_some.mpr hx
  have h₂ : M.kind.axis = none := Kind.axis_eq_none.mpr hk
  simp [exLabel, h₁, h₂, apexLabel, hU, Atom.conv, Direction.flip]

private theorem exLabel_v_reverse {x : D} {d : Axis} (hx : (S.lab x x).src = d.kind)
    (hk : M.kind = .zero) (hU : ¬UCond M.preLab M.newRoot d none (some x))
    (hV : VCond M.preLab M.newRoot M.WillTile d.other none (some x)) :
    M.exLabel T x = v d .reverse := by
  have h₁ : (S.lab x x).src.axis = some d := Kind.axis_eq_some.mpr hx
  have h₂ : M.kind.axis = none := Kind.axis_eq_none.mpr hk
  simp [exLabel, h₁, h₂, apexLabel, hU, hV, Atom.conv, Direction.flip]

include hS in
/-- The case of `Good.u_class` for the response in which one of the two nodes of the class is
the new node. -/
private theorem u_class_aux {h b a' : D} {d : Axis} (hh : M.ext T h = green d .forward)
    (hroot : M.newRoot (some h) none = M.newRoot (some h) (some a'))
    (hst : (M.ext T b).IsStep) : S.lab h b = green d .forward := by
  have hh' := M.par_of_ext_green hh
  obtain ⟨hb₁, hb⟩ := M.par_of_ext_isStep hst
  rw [hb₁] at hst
  obtain ⟨s, o, hs, hstep, -, -⟩ := M.exists_step_of_newRoot hS hh' hroot
  have hne : M.par h ≠ M.par s := by simp [hh', hstep]
  rcases M.eq_of_isPar (M.isPar_of_green hh') (M.isPar_of_isStep (by simp [hstep, Atom.IsStep]))
    hb hne with rfl | rfl
  · simp [hh', Atom.IsStep] at hst
  · exact hs

include hS in
private theorem u_class_next {h b : Option D} {d : Axis}
    (hU : UCond (M.next T).lab M.newRoot d h b) :
    (M.next T).lab h b = green d .forward ∨ (M.next T).lab h b = u d .forward := by
  have hpre := M.ucond_pre hU
  obtain ⟨a, a', ⟨hne, ha, ha', hroot⟩, hst, hst'⟩ := hU
  rcases h with _ | h <;> rcases b with _ | b
  · rcases a with _ | a
    · cases ha
    · have h₁ := M.par_of_ext_green (Atom.conv_eq_iff.mp ha)
      have hst₁ : (M.ext T a).IsStep := hst
      rw [(M.par_of_ext_isStep hst₁).1, h₁] at hst₁
      cases hst₁
  · obtain ⟨a, a', rfl, rfl, -, ha₁, ha₂, hall⟩ :=
      M.twin_none hne (M.preLab_of_green ha) (M.preLab_of_green ha')
    have hst₁ : (S.lab a b).IsStep := hst
    have hst₂ : (S.lab a' b).IsStep := hst'
    have hb : ¬M.IsPar b := fun hb => by
      rcases hall b hb with rfl | rfl
      · exact hS.ne_of_isStep hst₁ rfl
      · exact hS.ne_of_isStep hst₂ rfl
    obtain ⟨e, o, he⟩ := Atom.isStep_iff.mp hst₁
    have h₁ : (S.lab a a).src = e.kind := hS.typed.src_of_eq he
    have h₂ : (S.lab b b).src = e.kind := by rw [hS.typed.tgt_of_eq he, Atom.tgt_step]
    have h₃ : (S.lab a a).src = d.kind := by rw [← M.par_src hS a, ha₁, Atom.src_green_reverse]
    have h₄ : M.kind = .zero := by rw [← M.par_tgt a, ha₁, Atom.tgt_green_reverse]
    obtain rfl : e = d := Axis.kind_inj.mp (h₁.symm.trans h₃)
    right
    change (M.ext T b).conv = u e .forward
    rw [M.ext_of_not_isPar hb, M.exLabel_u_reverse h₂ h₄ hpre]
    rfl
  · rcases a with _ | a
    · cases hst
    rcases a' with _ | a'
    · cases hst'
    have ha₁ : S.lab h a = green d .forward := ha
    have ha₂ : S.lab h a' = green d .forward := ha'
    have hst₁ := M.par_of_ext_isStep (T := T) (x := a) hst
    have hst₂ := M.par_of_ext_isStep (T := T) (x := a') hst'
    have hne' : a ≠ a' := fun h => hne (congrArg _ h)
    have hha : h ≠ a := hS.ne_of_green ha₁
    have hha' : h ≠ a' := hS.ne_of_green ha₂
    have hh : ¬M.IsPar h := fun hh => by
      rcases M.isPar_three hh hst₁.2 hst₂.2 with h | h | h
      · exact hha h
      · exact hha' h
      · exact hne' h
    have hst₃ : (M.par a).IsStep := hst₁.1 ▸ hst
    obtain ⟨e, o, he⟩ := Atom.isStep_iff.mp hst₃
    have h₁ : (S.lab a a).src = e.kind := by rw [← M.par_src hS a, he, Atom.src_step]
    have h₂ : M.kind = e.kind := by rw [← M.par_tgt a, he, Atom.tgt_step]
    have h₃ : (S.lab a a).src = d.kind := hS.typed.tgt_of_eq ha₁
    have h₄ : (S.lab h h).src = .zero := hS.typed.src_of_eq ha₁
    obtain rfl : e = d := Axis.kind_inj.mp (h₁.symm.trans h₃)
    right
    change M.ext T h = u e .forward
    rw [M.ext_of_not_isPar hh, M.exLabel_u_forward h₄ h₂ hpre]
  · rcases a with _ | a <;> rcases a' with _ | a'
    · exact (hne rfl).elim
    · exact .inl (M.u_class_aux hS ha hroot (Atom.isStep_conv.mp hst))
    · exact .inl (M.u_class_aux hS ha' hroot.symm (Atom.isStep_conv.mp hst'))
    · exact hS.u_class ⟨a, a', ⟨fun h => hne (congrArg _ h), ha, ha', Option.some.inj hroot⟩,
        hst, hst'⟩

include hS in
/-- The case of `Good.v_class` for the response in which one of the two nodes of the class is
the new node. -/
private theorem v_class_aux {h y a' : D} {d : Axis} (hh : M.ext T h = green d .forward)
    (hroot : M.newRoot (some h) none = M.newRoot (some h) (some a'))
    (ht : (M.ext T y).IsTile) : S.lab h y = green d.other .forward := by
  have hh' := M.par_of_ext_green hh
  obtain ⟨s, o', -, hs, -, -⟩ := M.exists_step_of_newRoot hS hh' hroot
  have hstep : (M.par s).IsStep := by simp [hs, Atom.IsStep]
  have hps := M.isPar_of_isStep hstep
  obtain ⟨i, o, hi⟩ := Atom.isTile_iff.mp ht
  rcases M.ext_tile hi with hp | ⟨-, ⟨h₁, d₁, hy₁, hh₁⟩, -⟩
  · have hne : M.par h ≠ M.par s := fun heq => by simp [← heq, hh', Atom.IsStep] at hstep
    rcases M.eq_of_isPar (M.isPar_of_green hh') hps
      (M.isPar_of_isTile (x := y) (by simp [hp, Atom.IsTile])) hne with rfl | rfl
    · rw [hh'] at hp
      cases hp
    · rw [hp] at hstep
      cases hstep
  · obtain rfl := M.green_par_unique hps (.inr hstep) hh' hh₁
    obtain rfl : d₁.other = d := by simpa [hh₁] using hh'
    simpa using hy₁

include hS in
/-- The case of `Good.v_class` for the response in which tile edges join the new node to two nodes
of one class under `h`, and ∀ has labelled the edge from `h` to the new node. Were the label not
green, another node would see the new node and the two nodes of the class, against
`Good.apex_unique`. -/
private theorem v_class_par {h a a' : D} {d : Axis} (hh : M.IsPar h)
    (ha₁ : S.lab h a = green d .forward) (ha₂ : S.lab h a' = green d .forward) (hne' : a ≠ a')
    (hroot' : S.root h a = S.root h a') (ht₁ : (M.ext T a).IsTile)
    (ht₂ : (M.ext T a').IsTile) : M.par h = green d.other .forward := by
  by_contra hng
  have aux (a a' : D) (ha₁ : S.lab h a = green d .forward)
      (ha₂ : S.lab h a' = green d .forward) (hne' : a ≠ a')
      (hroot' : S.root h a = S.root h a') (ht₁ : (M.ext T a).IsTile)
      (ht₂ : (M.ext T a').IsTile) (hna : ¬M.IsPar a) : False := by
    obtain ⟨i, o, hi⟩ := Atom.isTile_iff.mp ht₁
    rcases M.ext_tile hi with hp | ⟨-, ⟨h₁, d₁, hy₁, hh₁⟩, -⟩
    · exact hna (M.isPar_of_isTile (by simp [hp, Atom.IsTile]))
    obtain rfl : d = d₁ :=
      Axis.kind_inj.mp ((hS.typed.tgt_of_eq ha₁).symm.trans (hS.typed.tgt_of_eq hy₁))
    have hh₁' : h₁ ≠ h := fun e => hng (e ▸ hh₁)
    have hna' : ¬M.IsPar a' := fun hpa' => by
      rcases M.isPar_three hh (M.isPar_of_green hh₁) hpa' with e | e | e
      · exact hh₁' e.symm
      · exact hS.ne_of_green ha₂ e
      · subst e
        have k₁ : (S.lab h₁ h₁).src = .zero := hS.typed.src_of_eq hy₁
        have k₂ : (S.lab h₁ h₁).src = d.kind := hS.typed.tgt_of_eq ha₂
        exact absurd (k₂.symm.trans k₁) (by simp)
    obtain ⟨i', o', hi'⟩ := Atom.isTile_iff.mp ht₂
    rcases M.ext_tile hi' with hp | ⟨-, ⟨h₂, d₂, hy₂, hh₂⟩, -⟩
    · exact hna' (M.isPar_of_isTile (by simp [hp, Atom.IsTile]))
    obtain rfl : d = d₂ :=
      Axis.kind_inj.mp ((hS.typed.tgt_of_eq ha₂).symm.trans (hS.typed.tgt_of_eq hy₂))
    obtain rfl : h₁ = h₂ := by
      rcases M.isPar_three hh (M.isPar_of_green hh₁) (M.isPar_of_green hh₂) with e | e | e
      · exact (hh₁' e.symm).elim
      · exact (hng (e ▸ hh₂)).elim
      · exact e
    exact hh₁' (hS.apex_unique ⟨hne', ha₁, ha₂, hroot'⟩ hy₁ hy₂).symm
  by_cases hna : M.IsPar a
  · by_cases hna' : M.IsPar a'
    · rcases M.isPar_three hh hna hna' with e | e | e
      · exact hS.ne_of_green ha₁ e
      · exact hS.ne_of_green ha₂ e
      · exact hne' e
    · exact aux a' a ha₂ ha₁ hne'.symm hroot'.symm ht₂ ht₁ hna'
  · exact aux a a' ha₁ ha₂ hne' hroot' ht₁ ht₂ hna

include hS in
private theorem v_class_next {h y : Option D} {d : Axis}
    (hV : VCond (M.next T).lab M.newRoot (fun a y => ((M.next T).lab a y).IsTile) d h y) :
    (M.next T).lab h y = green d.other .forward ∨ (M.next T).lab h y = v d.other .forward := by
  obtain ⟨a, a', ⟨hne, ha, ha', hroot⟩, ht, ht'⟩ := hV
  rcases h with _ | h <;> rcases y with _ | y
  · rcases a with _ | a
    · cases ha
    · have h₁ := M.par_of_ext_green (Atom.conv_eq_iff.mp ha)
      have ht₁ : (M.ext T a).IsTile := ht
      rw [M.ext_of_isPar (M.isPar_of_green h₁), h₁] at ht₁
      cases ht₁
  · have hpa := M.preLab_of_green ha
    have hpa' := M.preLab_of_green ha'
    obtain ⟨a, a', rfl, rfl, -, ha₁, ha₂, hall⟩ := M.twin_none hne hpa hpa'
    have ht₁ : (S.lab a y).IsTile := ht
    have ht₂ : (S.lab a' y).IsTile := ht'
    have hy : ¬M.IsPar y := fun hy => by
      rcases hall y hy with rfl | rfl
      · exact hS.ne_of_isTile ht₁ rfl
      · exact hS.ne_of_isTile ht₂ rfl
    obtain ⟨i, o, hi⟩ := Atom.isTile_iff.mp ht₁
    obtain ⟨d', rfl⟩ := o.exists_tileDir
    have h₁ : (S.lab a a).src = d'.kind := by rw [hS.typed.src_of_eq hi, Atom.src_tile]
    have h₂ : (S.lab y y).src = d'.other.kind := by rw [hS.typed.tgt_of_eq hi, Atom.tgt_tile]
    have h₃ : (S.lab a a).src = d.kind := by rw [← M.par_src hS a, ha₁, Atom.src_green_reverse]
    have h₄ : M.kind = .zero := by rw [← M.par_tgt a, ha₁, Atom.tgt_green_reverse]
    obtain rfl : d = d' := Axis.kind_inj.mp (h₃.symm.trans h₁)
    have hnU : ¬UCond M.preLab M.newRoot d.other none (some y) := by
      rintro ⟨b, b', ⟨hbne, hb, hb', -⟩, -, -⟩
      obtain ⟨_, _, -, -, -, hb₁, hb₂, hall'⟩ := M.twin_none hbne hb hb'
      rcases hall' a (M.isPar_of_green ha₁) with rfl | rfl
      · simp [ha₁] at hb₁
      · simp [ha₁] at hb₂
    have hVpre : VCond M.preLab M.newRoot M.WillTile d.other.other none (some y) := by
      rw [Axis.other_other]
      exact ⟨some a, some a', ⟨hne, hpa, hpa', hroot⟩, ht₁, ht₂⟩
    right
    change (M.ext T y).conv = v d.other .forward
    rw [M.ext_of_not_isPar hy, M.exLabel_v_reverse h₂ h₄ hnU hVpre]
    rfl
  · rcases a with _ | a
    · cases ht
    rcases a' with _ | a'
    · cases ht'
    have ha₁ : S.lab h a = green d .forward := ha
    have ha₂ : S.lab h a' = green d .forward := ha'
    have ht₁ : (M.ext T a).IsTile := ht
    have ht₂ : (M.ext T a').IsTile := ht'
    have hne' : a ≠ a' := fun h => hne (congrArg _ h)
    have hroot' : S.root h a = S.root h a' := Option.some.inj hroot
    have hVpre : VCond M.preLab M.newRoot M.WillTile d (some h) none :=
      ⟨some a, some a', ⟨hne, ha₁, ha₂, hroot⟩, M.willTile_of_isTile ht₁,
        M.willTile_of_isTile ht₂⟩
    by_cases hh : M.IsPar h
    · left
      change M.ext T h = green d.other .forward
      rw [M.ext_of_isPar hh]
      exact M.v_class_par hS hh ha₁ ha₂ hne' hroot' ht₁ ht₂
    · right
      change M.ext T h = v d.other .forward
      obtain ⟨i, o, hi⟩ := Atom.isTile_iff.mp ht₁
      obtain ⟨d', rfl⟩ := o.exists_tileDir
      have k₁ : (S.lab a a).src = d'.kind := by rw [← M.ext_src (T := T) hS a, hi, Atom.src_tile]
      have k₂ : M.kind = d'.other.kind := by rw [← M.ext_tgt (T := T) a, hi, Atom.tgt_tile]
      have k₃ : (S.lab a a).src = d.kind := hS.typed.tgt_of_eq ha₁
      have k₄ : (S.lab h h).src = .zero := hS.typed.src_of_eq ha₁
      obtain rfl : d = d' := Axis.kind_inj.mp (k₃.symm.trans k₁)
      have hnU : ¬UCond M.preLab M.newRoot d.other (some h) none := by
        rintro ⟨b, b', ⟨hbne, -, -, -⟩, hb, hb'⟩
        rcases b with _ | b
        · cases hb
        rcases b' with _ | b'
        · cases hb'
        have hb₁ : (M.par b).IsStep := hb
        have hb₂ : (M.par b').IsStep := hb'
        rcases M.ext_tile hi with hp | ⟨-, ⟨h₁, d₁, -, hh₁⟩, -⟩
        · refine M.not_isPar_of_twins (M.isPar_of_isStep hb₁) (M.isPar_of_isStep hb₂)
            (fun h => hbne (congrArg _ h)) ?_ ?_
            (M.isPar_of_isTile (x := a) (by simp [hp, Atom.IsTile])) <;> intro e
          · simp [← e, hp, Atom.IsStep] at hb₁
          · simp [← e, hp, Atom.IsStep] at hb₂
        · refine M.not_isPar_of_twins (M.isPar_of_isStep hb₁) (M.isPar_of_isStep hb₂)
            (fun h => hbne (congrArg _ h)) ?_ ?_ (M.isPar_of_green hh₁) <;> intro e
          · simp [← e, hh₁, Atom.IsStep] at hb₁
          · simp [← e, hh₁, Atom.IsStep] at hb₂
      rw [M.ext_of_not_isPar hh, M.exLabel_v_forward k₄ k₂ hnU (by rwa [Axis.other_other])]
  · rcases a with _ | a <;> rcases a' with _ | a'
    · exact (hne rfl).elim
    · exact .inl (M.v_class_aux hS ha hroot (Atom.isTile_conv.mp ht))
    · exact .inl (M.v_class_aux hS ha' hroot.symm (Atom.isTile_conv.mp ht'))
    · exact hS.v_class ⟨a, a', ⟨fun h => hne (congrArg _ h), ha, ha', Option.some.inj hroot⟩,
        ht, ht'⟩

include hS in
/-- The move has no witness: no old node sees both nodes picked by ∀ when he asks for green
edges from the new node to them. -/
private theorem not_green_green {h' a a' : D} {d : Axis} (ha : M.par a = green d .reverse)
    (ha' : M.par a' = green d .reverse) (hne : a ≠ a') (hb : S.lab h' a = green d .forward)
    (hb' : S.lab h' a' = green d .forward) : False := by
  have hp := M.par_p
  have hq := M.par_q hS
  have key (a a' : D) (ha : M.par a = green d .reverse) (ha' : M.par a' = green d .reverse)
      (hb : S.lab h' a = green d .forward) (hb' : S.lab h' a' = green d .forward)
      (hap : a = M.p) (haq : a' = M.q) : False := by
    subst hap haq
    refine M.fresh h' ?_ ?_
    · rw [hS.typed.eq_conv hb, ← hp, ha]
      rfl
    · rw [hb', ← conv_conv M.b, ← hq, ha']
      rfl
  rcases M.isPar_of_green ha with rfl | rfl <;> rcases M.isPar_of_green ha' with rfl | rfl
  · exact hne rfl
  · exact key _ _ ha ha' hb hb' rfl rfl
  · exact key _ _ ha' ha hb' hb rfl rfl
  · exact hne rfl

include hS in
private theorem apex_unique_next {h h' a a' : Option D} {d : Axis}
    (htw : Twin (M.next T).lab M.newRoot d h a a')
    (hb : (M.next T).lab h' a = green d .forward)
    (hb' : (M.next T).lab h' a' = green d .forward) : h = h' := by
  obtain ⟨hne, ha, ha', hroot⟩ := htw
  rcases h with _ | h <;> rcases h' with _ | h'
  · rfl
  · exfalso
    obtain ⟨a, a', rfl, rfl, hne', h₁, h₂, -⟩ :=
      M.twin_none hne (M.preLab_of_green ha) (M.preLab_of_green ha')
    exact M.not_green_green hS h₁ h₂ hne' hb hb'
  · exfalso
    obtain ⟨a, a', rfl, rfl, hne', h₁, h₂, -⟩ :=
      M.twin_none hne (M.preLab_of_green hb) (M.preLab_of_green hb')
    exact M.not_green_green hS h₁ h₂ hne' ha ha'
  · rcases a with _ | a <;> rcases a' with _ | a'
    · exact (hne rfl).elim
    · obtain ⟨s, o, -, hs, -, -⟩ := M.exists_step_of_newRoot hS (M.par_of_ext_green ha) hroot
      have hstep : (M.par s).IsStep := by simp [hs, Atom.IsStep]
      exact congrArg some (M.green_par_unique (M.isPar_of_isStep hstep) (.inr hstep)
        (M.par_of_ext_green ha) (M.par_of_ext_green hb))
    · obtain ⟨s, o, -, hs, -, -⟩ :=
        M.exists_step_of_newRoot hS (M.par_of_ext_green ha') hroot.symm
      have hstep : (M.par s).IsStep := by simp [hs, Atom.IsStep]
      exact congrArg some (M.green_par_unique (M.isPar_of_isStep hstep) (.inr hstep)
        (M.par_of_ext_green ha') (M.par_of_ext_green hb'))
    · exact congrArg some (hS.apex_unique
        ⟨fun h => hne (congrArg _ h), ha, ha', Option.some.inj hroot⟩ hb hb')

include hS in
private theorem tile_idx_next {x y : Option D} {i : Fin L.length} {o : Direction}
    (h : (M.next T).lab x y = tile i o) : i = T.idx ((M.next T).cell x y) := by
  rcases x with _ | x <;> rcases y with _ | y
  · cases h
  · exact M.tile_idx_ext (Atom.conv_eq_iff.mp h)
  · exact M.tile_idx_ext h
  · exact hS.tile_idx h

include hS in
/-- The case of `Good.cell_class` for the response in which one of the two nodes of the class is
the new node. -/
private theorem cell_class_aux {h b y : D} {d : Axis} (hh : M.ext T h = green d .forward)
    (hb : S.lab h b = green d .forward) (hy : S.lab h y = green d.other .forward)
    (hr : M.newRoot (some h) none = M.newRoot (some h) (some b)) :
    (S.cell b y).seed = (M.cellAt y).seed ∧ ((M.cellAt y).seed ≠ 0 →
      (S.cell b y).pos = (M.cellAt y).pos + (S.pot h b - M.newPot (some h) none) • d.vec) := by
  have hh' := M.par_of_ext_green hh
  obtain ⟨s, o, hs, he, hroot, hpot⟩ := M.exists_step_of_newRoot hS hh' hr
  have hsy : (S.lab s y).IsTile := hS.isTile_of_green hs hy
  have hys : (S.lab y s).IsTile := by
    rw [← hS.typed.conv_lab]
    exact Atom.isTile_conv.mpr hsy
  have hA : M.Apex y := ⟨h, d.other, hy, by rw [Axis.other_other]; exact hh'⟩
  obtain ⟨c₁, c₂⟩ := M.cellAt_of_step hS he hys hA
  obtain ⟨l₁, l₂⟩ := hS.cell_class hs hb hy hroot
  rw [hS.cell_symm s y] at l₁ l₂
  refine ⟨l₁.trans c₁.symm, fun h0 => ?_⟩
  rw [c₁] at h0
  rw [l₂ h0, c₂ h0, hpot]
  module

include hS in
private theorem cell_class_next {h a b y : Option D} {d : Axis}
    (ha : (M.next T).lab h a = green d .forward) (hb : (M.next T).lab h b = green d .forward)
    (hy : (M.next T).lab h y = green d.other .forward) (hr : M.newRoot h a = M.newRoot h b) :
    ((M.next T).cell b y).seed = ((M.next T).cell a y).seed ∧
      (((M.next T).cell a y).seed ≠ 0 → ((M.next T).cell b y).pos =
        ((M.next T).cell a y).pos + (M.newPot h b - M.newPot h a) • d.vec) := by
  by_cases hab : a = b
  · subst hab
    simp
  rcases h with _ | h
  · exfalso
    obtain ⟨a, b, rfl, rfl, -, ha₁, hb₁, hall⟩ :=
      M.twin_none hab (M.preLab_of_green ha) (M.preLab_of_green hb)
    rcases y with _ | y
    · cases hy
    have hy₁ : M.par y = green d.other .reverse := M.par_of_ext_green (Atom.conv_eq_iff.mp hy)
    rcases hall y (M.isPar_of_green hy₁) with rfl | rfl
    · simp [hy₁] at ha₁
    · simp [hy₁] at hb₁
  rcases y with _ | y
  · have hh := M.par_of_ext_green hy
    rcases a with _ | a
    · have h₁ : green d .forward = green d.other .forward := ha.symm.trans hy
      simp at h₁
    rcases b with _ | b
    · have h₁ : green d .forward = green d.other .forward := hb.symm.trans hy
      simp at h₁
    have ha₁ : S.lab h a = green d .forward := ha
    have hb₁ : S.lab h b = green d .forward := hb
    have hr' : S.root h a = S.root h b := Option.some.inj hr
    change (M.cellAt b).seed = (M.cellAt a).seed ∧ ((M.cellAt a).seed ≠ 0 →
      (M.cellAt b).pos = (M.cellAt a).pos + (S.pot h b - S.pot h a) • d.vec)
    by_cases hc : ∃ m, M.Cand a m
    · obtain ⟨m, hm⟩ := hc
      obtain ⟨a₁, a₂⟩ := M.cellAt_spec hS hm
      obtain ⟨b₁, b₂⟩ := M.cellAt_spec hS (M.cand_of_class hm hh ha₁ hb₁ hr')
      refine ⟨b₁.trans a₁.symm, fun h0 => ?_⟩
      rw [a₁] at h0
      rw [b₂ h0, a₂ h0]
    · have hc' : ¬∃ m, M.Cand b m := fun ⟨m, hm⟩ =>
        hc ⟨_, M.cand_of_class hm hh hb₁ ha₁ hr'.symm⟩
      have hta : ¬(M.par a).IsTile := fun ht => by
        obtain ⟨j, o, hj⟩ := Atom.isTile_iff.mp ht
        exact hc ⟨_, M.cand_self hS hh ha₁ hj⟩
      have htb : ¬(M.par b).IsTile := fun ht => by
        obtain ⟨j, o, hj⟩ := Atom.isTile_iff.mp ht
        exact hc' ⟨_, M.cand_self hS hh hb₁ hj⟩
      rw [M.cellAt_of_not hc hta, M.cellAt_of_not hc' htb]
      exact ⟨rfl, fun h0 => (h0 rfl).elim⟩
  · rcases a with _ | a <;> rcases b with _ | b
    · exact (hab rfl).elim
    · exact M.cell_class_aux hS ha hb hy hr
    · obtain ⟨h₁, h₂⟩ := M.cell_class_aux hS hb ha hy hr.symm
      refine ⟨h₁.symm, fun h0 => ?_⟩
      change (M.cellAt y).pos = (S.cell a y).pos + (M.newPot (some h) none - S.pot h a) • d.vec
      rw [h₂ (h₁ ▸ h0)]
      module
    · exact hS.cell_class ha hb hy (Option.some.inj hr)

include hS in
/-- The response of ∃ to a move satisfies the invariant. -/
private theorem good_next : Good T (M.next T) where
  typed := M.typed_next hS
  isUnit_iff := M.isUnit_iff_next hS
  rule_free := M.rule_free_next hS
  step_class := M.step_class_next hS
  u_class := M.u_class_next hS
  v_class := M.v_class_next hS
  apex_unique := M.apex_unique_next hS
  cell_symm x y := by
    rcases x with _ | x <;> rcases y with _ | y <;> first | rfl | exact hS.cell_symm x y
  tile_idx := M.tile_idx_next hS
  cell_class := M.cell_class_next hS





end Move

/-! ### The winning strategy -/

variable (T) in
/-- The networks that ∃ plays: those of the labellings that satisfy the invariant, with their
nodes numbered. -/
private def winning (n : ℕ) : Set (AtomicNetwork (tilingFrame L) (Fin n)) :=
  {N | ∃ (D : Type) (S : Ann L D) (hS : Good T S) (e : Fin n ≃ D),
    N = hS.network.comap e.toEmbedding}

private theorem hasWinningStrategy_of_tilings (T : Tilings L) :
    (tilingFrame L).HasWinningStrategy := by
  refine .of_forall_exists_comap_castSucc (winning T) (fun a => ?_) ?_
  · by_cases ha : a.IsUnit
    · refine ⟨1, _, ⟨Unit, _, Ann.good_single a.src, finOneEquiv, rfl⟩, 0, 0, ?_⟩
      exact ha.eq_unit.symm
    · exact ⟨2, _, ⟨Bool, _, Ann.good_pair ha, finTwoEquiv, rfl⟩, 0, 1, rfl⟩
  · rintro n _ ⟨D, S, hS, e, rfl⟩ i j a b hab hfresh
    have hfresh' (w : D) (hw : S.lab (e i) w = a) : S.lab w (e j) ≠ b := by
      simpa [Good.network, hw] using hfresh (e.symm w)
    let M : Move S := ⟨e i, e j, a, b, hab, hfresh'⟩
    refine ⟨_, ⟨Option D, _, M.good_next hS, finSuccEquivLast.trans (Equiv.optionCongr e), rfl⟩,
      ?_, ?_, ?_⟩
    · ext x y
      simp [Good.network, M.next_lab_some]
    · simpa [Good.network] using M.next_lab_p (T := T)
    · simpa [Good.network] using M.next_lab_q hS

end Tiling

open Tiling

/-- Theorem 4 of [HirschHodkinson2001], Section 6: if every position of `L` is at the origin of a
tiling by positions of `L`, and the tile at position `0` matches itself horizontally and
vertically, then ∃ has a winning strategy in the game on `tilingFrame L`. The source asks that the
tile `T₀` have one colour on its four edges, used by no other tile; the strategy labels with `T₀`
the tile edges that it does not place in a tiling, for which the two equations suffice. -/
public theorem hasWinningStrategy_tilingFrame {L : List WangTile} (hL : 0 < L.length)
    (hrow : L[0].right = L[0].left) (hcol : L[0].top = L[0].bottom) (h : EveryIndexOccurs L) :
    (tilingFrame L).HasWinningStrategy := by
  have : NeZero L.length := ⟨hL.ne'⟩
  choose F hF₀ hF using h
  refine hasWinningStrategy_of_tilings
    { til := fun σ c => if σ = 0 then 0 else F σ c.1 c.2
      til_zero := fun c => by simp
      til_origin := fun σ => by by_cases hσ : σ = 0 <;> simp [hσ, hF₀]
      til_match := fun σ c d => ?_ }
  by_cases hσ : σ = 0
  · cases d <;> simp [hσ, Axis.front, Axis.back, hrow, hcol]
  · cases d
    · simpa [hσ, Axis.front, Axis.back, Axis.vec] using (hF σ c.1 c.2).1
    · simpa [hσ, Axis.front, Axis.back, Axis.vec] using (hF σ c.1 c.2).2

end Cslib.RelationAlgebra
