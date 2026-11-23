/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
public import CslibFrontier.Foundations.RelationAlgebra.AtomicNetwork
import Mathlib.Tactic.IntervalCases

/-!
# The relation algebra of a list of Wang tiles

Hirsch and Hodkinson associate with a finite set `τ` of Wang tiles a finite algebra `RA(τ)` whose
networks force the tile atoms to form tilings [HirschHodkinson2001], Section 4. It has `2k + 28`
atoms for `k` tiles, and is given by a converse, three identity atoms and a list of inconsistent
triangles. It need not be associative, so it is defined here as an `AtomStructure`, which does not
include the laws (`LawfulAtomStructure`).

The tiles are given as a list `L`, and the tile atoms are indexed by the positions of `L`, so that
a repeated tile contributes two atoms for each of its positions. The tile at position `0` plays
the part of the source's special tile `T₀`: rule 3 exempts it, and nothing else is asked of it in
the definition.

## Conventions

A cycle `(r, s, t)` of a frame means `t ≤ r;s`, whereas the source's triangle `(a, b, c)` is
consistent when `c˘ ≤ a;b`. The source's triangle `(a, b, c)` is therefore the triple
`(a, b, c˘)` here, and its six Peircean transforms are the triples
`(r, s, t)`, `(s, t˘, r˘)`, `(t˘, r, s˘)`, `(r˘, t, s)`, `(t, s˘, r)` and `(s˘, r˘, t˘)`.

## Main definitions

* `Cslib.RelationAlgebra.Tiling.Atom`: the atoms of `RA(τ)`, with their converse `Atom.conv` and
  the kinds `Atom.src`, `Atom.tgt` of node at which their edges start and end.
* `Cslib.RelationAlgebra.Tiling.Rule`: rules 1–4 of the source and the duals of rules 2–4.
* `Cslib.RelationAlgebra.Tiling.Cycle`: the consistent triangles.
* `Cslib.RelationAlgebra.tilingFrame`: the frame of `RA(τ)`.
* `Cslib.RelationAlgebra.Tiling.network`: networks over the frame, from labellings that avoid the
  rules.
* `Cslib.RelationAlgebra.Tiling.Atom.code`, `Atom.equivFin`: the numbering of the atoms, a
  bijection with `Fin (2 * k + 28)`.

## Main results

* `Cslib.RelationAlgebra.Tiling.Cycle.exists_eq_tile`: by rule 1, an edge from a `1`-node to a
  `2`-node under a common green apex is labelled by a tile atom.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

@[expose] public section

namespace Cslib.RelationAlgebra

namespace Tiling

/-- The three kinds of node in a network over `RA(τ)`. The identity of `RA(τ)` is the join of
three units `e₀`, `e₁`, `e₂`, and a node is an `i`-node when its loop is labelled `eᵢ`. -/
inductive Kind where
  /-- The `0`-nodes, the apexes of green edges. -/
  | zero
  /-- The `1`-nodes, which index the columns of a tiling. -/
  | one
  /-- The `2`-nodes, which index the rows of a tiling. -/
  | two
deriving DecidableEq

/-- The two kinds of node other than `0`, which are also the two axes of the plane: steps between
`1`-nodes move along the first coordinate, and steps between `2`-nodes along the second. -/
inductive Axis where
  /-- The kind `1`, and the first coordinate. -/
  | one
  /-- The kind `2`, and the second coordinate. -/
  | two
deriving DecidableEq

/-- The kind of node named by an axis. -/
def Axis.kind : Axis → Kind
  | one => .one
  | two => .two

/-- An atom that is not its own converse is either the forward atom of its pair or the reverse
one, which is the converse of the forward atom. -/
inductive Direction where
  /-- The atoms `g₀ᵢ`, `u₀ᵢ`, `v₀ᵢ`, `+1ᵢ` and `T₁₂ⁱ` of the source. -/
  | forward
  /-- Their converses `gᵢ₀`, `uᵢ₀`, `vᵢ₀`, `-1ᵢ` and `T₂₁ⁱ`. -/
  | reverse
deriving DecidableEq

/-- The other direction. -/
def Direction.flip : Direction → Direction
  | forward => reverse
  | reverse => forward

@[simp]
theorem Direction.flip_flip (o : Direction) : o.flip.flip = o := by cases o <;> rfl

/-- The atoms of `RA(τ)` for tiles indexed by `ι` [HirschHodkinson2001], Section 4.1: there are
`2k + 28` of them when `ι` has `k` elements. -/
inductive Atom (ι : Type*) where
  /-- The unit `eᵢ`, the part of the identity on the `i`-nodes. -/
  | unit (i : Kind)
  /-- The white atom `wᵢⱼ` from `i`-nodes to `j`-nodes; the source writes `wᵢ` for `wᵢᵢ`. -/
  | white (i j : Kind)
  /-- The green atom `g₀d` from `0`-nodes to `d`-nodes, and its converse `g_d0`. -/
  | green (d : Axis) (o : Direction)
  /-- The atom `u₀d` from `0`-nodes to `d`-nodes, and its converse `u_d0`. -/
  | u (d : Axis) (o : Direction)
  /-- The atom `v₀d` from `0`-nodes to `d`-nodes, and its converse `v_d0`. -/
  | v (d : Axis) (o : Direction)
  /-- The step `+1_d` between `d`-nodes, and its converse `-1_d`. -/
  | step (d : Axis) (o : Direction)
  /-- The tile atom `T₁₂ⁱ` from `1`-nodes to `2`-nodes, and its converse `T₂₁ⁱ`. -/
  | tile (i : ι) (o : Direction)
deriving DecidableEq

namespace Atom

variable {ι : Type*}

/-- The converse of an atom [HirschHodkinson2001], Section 4.2. -/
def conv : Atom ι → Atom ι
  | unit i => unit i
  | white i j => white j i
  | green d o => green d o.flip
  | u d o => u d o.flip
  | v d o => v d o.flip
  | step d o => step d o.flip
  | tile i o => tile i o.flip

/-- The kind of node at which the edges labelled by an atom start: the index of the source's
start unit. -/
def src : Atom ι → Kind
  | unit i | white i _ => i
  | green _ .forward | u _ .forward | v _ .forward => .zero
  | green d .reverse | u d .reverse | v d .reverse | step d _ => d.kind
  | tile _ .forward => .one
  | tile _ .reverse => .two

/-- The kind of node at which the edges labelled by an atom end: the index of the source's end
unit. -/
def tgt (a : Atom ι) : Kind := a.conv.src

/-- The identity atoms are the three units. -/
def IsUnit : Atom ι → Prop
  | unit _ => True
  | _ => False

instance : DecidablePred (IsUnit : Atom ι → Prop) := fun a => by
  cases a <;> first | exact isTrue trivial | exact isFalse id

@[simp]
theorem conv_conv (a : Atom ι) : a.conv.conv = a := by cases a <;> simp [conv]

@[simp]
theorem isUnit_conv {a : Atom ι} : a.conv.IsUnit ↔ a.IsUnit := by cases a <;> exact .rfl

end Atom

open Atom

/-- The inconsistent triangles listed in [HirschHodkinson2001], Section 4.2: rule 1, rules 2–4
and the duals of rules 2–4, which exchange the kinds `1` and `2`, left with bottom and right with
top. The triple `(r, s, t)` is the source's triangle `(r, s, t˘)`; in particular the step `+1` of
the source's rule 2 appears here as its converse. The colours compared are those of the tiles at
the two positions of `L`, and rule 3 concerns every position but `0`. -/
def Rule (L : List WangTile) :
    Atom (Fin L.length) → Atom (Fin L.length) → Atom (Fin L.length) → Prop
  | green .one .reverse, green .two .forward, white .one .two => True
  | tile i .forward, tile j .reverse, step .one .reverse => L[i].left ≠ L[j].right
  | tile i .reverse, tile j .forward, step .two .reverse => L[i].bottom ≠ L[j].top
  | u .one .reverse, green .two .forward, tile i .forward => i.val ≠ 0
  | u .two .reverse, green .one .forward, tile i .reverse => i.val ≠ 0
  | v .one .reverse, green .one .forward, step .one _ => True
  | v .two .reverse, green .two .forward, step .two _ => True
  | _, _, _ => False

-- By cases on the atoms, so that `decide` can evaluate the instance in other modules.
instance (L : List WangTile) (r s t : Atom (Fin L.length)) : Decidable (Rule L r s t) := by
  rcases r with _ | _ | ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ | _ | ⟨i, _ | _⟩ <;>
    (try exact isFalse id) <;>
  rcases s with _ | _ | ⟨_ | _, _ | _⟩ | _ | _ | _ | ⟨j, _ | _⟩ <;> (try exact isFalse id) <;>
  rcases t with _ | ⟨_ | _ | _, _ | _ | _⟩ | _ | _ | _ | ⟨_ | _, _ | _⟩ | ⟨k, _ | _⟩ <;>
  first
    | exact isFalse id
    | exact isTrue trivial
    | (dsimp only [Rule]; infer_instance)

/-- A triangle is forbidden when it or one of its five other Peircean transforms is listed in
`Rule`. -/
def Forbidden (L : List WangTile) (r s t : Atom (Fin L.length)) : Prop :=
  Rule L r s t ∨ Rule L s t.conv r.conv ∨ Rule L t.conv r s.conv ∨
    Rule L r.conv t s ∨ Rule L t s.conv r ∨ Rule L s.conv r.conv t.conv

instance (L : List WangTile) (r s t : Atom (Fin L.length)) : Decidable (Forbidden L r s t) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The consistent triangles of `RA(τ)`, as triples `(r, s, t)` with `t ≤ r;s`
[HirschHodkinson2001], Section 4.2: the kinds of node match, a triangle with an identity atom is
degenerate, and the triangle is not forbidden. -/
structure Cycle (L : List WangTile) (r s t : Atom (Fin L.length)) : Prop where
  /-- The edge labelled `s` starts where the edge labelled `r` ends. -/
  tgt_eq_src : r.tgt = s.src
  /-- The edges labelled `r` and `t` start at the same kind of node. -/
  src_eq_src : r.src = t.src
  /-- The edges labelled `s` and `t` end at the same kind of node. -/
  tgt_eq_tgt : s.tgt = t.tgt
  /-- The source's `(eᵢ, x, y)` is inconsistent unless `x = y˘`. -/
  eq_of_isUnit_left : r.IsUnit → t = s
  /-- The transform of that rule in which the unit is the second atom. -/
  eq_of_isUnit_right : s.IsUnit → t = r
  /-- The transform of that rule in which the unit is the third atom. -/
  eq_conv_of_isUnit : t.IsUnit → s = r.conv
  /-- Neither the triangle nor any of its Peircean transforms is listed in `Rule`. -/
  not_forbidden : ¬Forbidden L r s t

theorem cycle_iff {L : List WangTile} {r s t : Atom (Fin L.length)} :
    Cycle L r s t ↔ r.tgt = s.src ∧ r.src = t.src ∧ s.tgt = t.tgt ∧ (r.IsUnit → t = s) ∧
      (s.IsUnit → t = r) ∧ (t.IsUnit → s = r.conv) ∧ ¬Forbidden L r s t :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩

instance (L : List WangTile) (r s t : Atom (Fin L.length)) : Decidable (Cycle L r s t) :=
  decidable_of_iff' _ cycle_iff

/-- By rule 1, an edge from a `1`-node to a `2`-node that some `0`-node joins by green edges is
labelled by a tile atom: the atoms from `1`-nodes to `2`-nodes are the tile atoms and the white
atom `w₁₂`, which rule 1 forbids here. -/
theorem Cycle.exists_eq_tile {L : List WangTile} {t : Atom (Fin L.length)}
    (h : Cycle L (green .one .reverse) (green .two .forward) t) : ∃ i, t = tile i .forward := by
  have hsrc : Kind.one = t.src := h.src_eq_src
  have htgt : Kind.two = t.tgt := h.tgt_eq_tgt
  have hrule : ¬Rule L (green .one .reverse) (green .two .forward) t := fun hr =>
    h.not_forbidden (.inl hr)
  rcases t with i | ⟨i, j⟩ | ⟨d, o⟩ | ⟨d, o⟩ | ⟨d, o⟩ | ⟨d, o⟩ | ⟨i, o⟩
  case unit => cases hsrc; cases htgt
  case white => cases hsrc; cases htgt; exact (hrule trivial).elim
  case tile => cases o <;> first | exact ⟨i, rfl⟩ | cases hsrc
  all_goals cases d <;> cases o <;> first | (cases hsrc; done) | cases htgt

end Tiling

open Tiling

/-- The frame of the algebra `RA(τ)` of [HirschHodkinson2001], Section 4, for the tiles listed in
`L`: its atoms, their converses, the three identity atoms and the consistent triangles. The tile
at position `0` is the one exempted by rule 3. The algebra need not be associative, so this is a
frame and not an atom structure. -/
def tilingFrame (L : List WangTile) : AtomStructure (Atom (Fin L.length)) where
  conv := Atom.conv
  id := {a | a.IsUnit}
  cycles := {(r, s, t) | Cycle L r s t}

instance (L : List WangTile) : DecidablePred (· ∈ (tilingFrame L).cycles) := fun (r, s, t) =>
  inferInstanceAs (Decidable (Cycle L r s t))

/-- A network over the frame of `RA(τ)`, from a labelling of the ordered pairs of nodes in which
the loops are the edges with unit labels, reversed edges carry converse atoms, every label starts
at the kind of its first node, and no three nodes, taken in any order, form a triangle listed in
`Rule`. The six Peircean transforms of a triangle of a network are its six orderings, so the rules
need to be checked only as listed. -/
@[simps]
def Tiling.network {L : List WangTile} {D : Type*} (label : D → D → Atom (Fin L.length))
    (kind : D → Kind) (isUnit_label : ∀ d e, (label d e).IsUnit ↔ d = e)
    (conv_label : ∀ d e, (label d e).conv = label e d)
    (src_label : ∀ d e, (label d e).src = kind d)
    (not_rule : ∀ d e f, ¬Rule L (label d e) (label e f) (label d f)) :
    AtomicNetwork (tilingFrame L) D where
  label := label
  label_mem_id := isUnit_label _ _
  conv_label := conv_label
  label_mem_cycles d e f :=
    { tgt_eq_src := by rw [Atom.tgt, conv_label, src_label, src_label]
      src_eq_src := by rw [src_label, src_label]
      tgt_eq_tgt := by rw [Atom.tgt, Atom.tgt, conv_label, conv_label, src_label, src_label]
      eq_of_isUnit_left := fun h => by rw [(isUnit_label d e).mp h]
      eq_of_isUnit_right := fun h => by rw [(isUnit_label e f).mp h]
      eq_conv_of_isUnit := fun h => by rw [conv_label, (isUnit_label d f).mp h]
      not_forbidden := by
        simp only [Forbidden, conv_label, not_or]
        exact ⟨not_rule _ _ _, not_rule _ _ _, not_rule _ _ _, not_rule _ _ _, not_rule _ _ _,
          not_rule _ _ _⟩ }

end Cslib.RelationAlgebra

end

/-! ### The numbering of the atoms -/

public section

namespace Cslib.RelationAlgebra.Tiling

/-- The number of a kind of node. -/
@[expose] def Kind.toNat : Kind → ℕ
  | zero => 0
  | one => 1
  | two => 2

/-- The axes are numbered `0` and `1`. -/
@[expose] def Axis.toNat : Axis → ℕ
  | one => 0
  | two => 1

/-- The forward direction is numbered `0` and the reverse direction `1`. -/
@[expose] def Direction.toNat : Direction → ℕ
  | forward => 0
  | reverse => 1

namespace Atom

variable {k : ℕ}

/-- The number of an atom of `RA(τ)` for `k` tiles, among `0, …, 2k + 27`:

| numbers | atoms |
|---|---|
| `0, 1, 2` | `e₀, e₁, e₂` |
| `3 + 3i + j` | `wᵢⱼ` |
| `12, 13, 14, 15` | `+1₁, -1₁, +1₂, -1₂` |
| `16, 17, 18, 19` | `g₀₁, g₁₀, g₀₂, g₂₀` |
| `20, 21, 22, 23` | `u₀₁, u₁₀, u₀₂, u₂₀` |
| `24, 25, 26, 27` | `v₀₁, v₁₀, v₀₂, v₂₀` |
| `28 + 2i, 29 + 2i` | `T₁₂ⁱ, T₂₁ⁱ` |
-/
@[expose] def code : Atom (Fin k) → ℕ
  | unit i => i.toNat
  | white i j => 3 + 3 * i.toNat + j.toNat
  | step d o => 12 + 2 * d.toNat + o.toNat
  | green d o => 16 + 2 * d.toNat + o.toNat
  | u d o => 20 + 2 * d.toNat + o.toNat
  | v d o => 24 + 2 * d.toNat + o.toNat
  | tile i o => 28 + 2 * i + o.toNat

theorem code_lt (a : Atom (Fin k)) : a.code < 2 * k + 28 := by
  rcases a with i | ⟨i, j⟩ | ⟨d, o⟩ | ⟨d, o⟩ | ⟨d, o⟩ | ⟨d, o⟩ | ⟨i, o⟩
  case tile => cases o <;> simp only [code, Direction.toNat] <;> omega
  case unit => cases i <;> simp only [code, Kind.toNat] <;> omega
  case white => cases i <;> cases j <;> simp only [code, Kind.toNat] <;> omega
  all_goals cases d <;> cases o <;> simp only [code, Axis.toNat, Direction.toNat] <;> omega

private def kindOf : ℕ → Kind
  | 0 => .zero
  | 1 => .one
  | _ => .two

private def axisOf : ℕ → Axis
  | 0 => .one
  | _ => .two

private def directionOf : ℕ → Direction
  | 0 => .forward
  | _ => .reverse

/-- The atom with a given number. -/
private def decode (n : Fin (2 * k + 28)) : Atom (Fin k) :=
  if h : 28 ≤ n.val then tile ⟨(n - 28) / 2, by omega⟩ (directionOf (n % 2))
  else if 24 ≤ n.val then v (axisOf ((n - 24) / 2)) (directionOf (n % 2))
  else if 20 ≤ n.val then u (axisOf ((n - 20) / 2)) (directionOf (n % 2))
  else if 16 ≤ n.val then green (axisOf ((n - 16) / 2)) (directionOf (n % 2))
  else if 12 ≤ n.val then step (axisOf ((n - 12) / 2)) (directionOf (n % 2))
  else if 3 ≤ n.val then white (kindOf ((n - 3) / 3)) (kindOf (n % 3))
  else unit (kindOf n)

/-- `RA(τ)` has `2k + 28` atoms for `k` tiles: the numbering `Atom.code` is a bijection. -/
def equivFin : Atom (Fin k) ≃ Fin (2 * k + 28) where
  toFun a := ⟨a.code, a.code_lt⟩
  invFun := decode
  left_inv a := by
    rcases a with i | ⟨i, j⟩ | ⟨d, o⟩ | ⟨d, o⟩ | ⟨d, o⟩ | ⟨d, o⟩ | ⟨i, o⟩
    case tile =>
      have h : 28 ≤ 28 + 2 * i.val + o.toNat := by omega
      have h₁ : (28 + 2 * i.val + o.toNat - 28) / 2 = i := by
        cases o <;> simp only [Direction.toNat] <;> omega
      have h₂ : directionOf ((28 + 2 * i.val + o.toNat) % 2) = o := by
        cases o <;> simp [Direction.toNat, directionOf, Nat.add_mod]
      simp only [decode, code, h, ↓reduceDIte, h₁, h₂, Fin.eta]
    case unit => cases i <;> simp [decode, code, Kind.toNat, kindOf]
    case white => cases i <;> cases j <;> simp [decode, code, Kind.toNat, kindOf]
    all_goals cases d <;> cases o <;>
      simp [decode, code, Axis.toNat, Direction.toNat, axisOf, directionOf]
  right_inv n := by
    obtain ⟨n, hn⟩ := n
    by_cases h : 28 ≤ n
    · obtain h2 | h2 := Nat.mod_two_eq_zero_or_one n <;>
        simp [decode, code, h, h2, Direction.toNat, directionOf] <;> omega
    · have : n < 28 := by omega
      interval_cases n <;>
        simp [decode, code, Kind.toNat, Axis.toNat, Direction.toNat, kindOf, axisOf, directionOf]

@[simp]
theorem coe_equivFin (a : Atom (Fin k)) : (equivFin a : ℕ) = a.code := by rfl

theorem code_injective : Function.Injective (code : Atom (Fin k) → ℕ) := fun _ _ h =>
  equivFin.injective (Fin.ext h)

instance : Finite (Atom (Fin k)) := .of_equiv _ equivFin.symm

end Atom

end Cslib.RelationAlgebra.Tiling
