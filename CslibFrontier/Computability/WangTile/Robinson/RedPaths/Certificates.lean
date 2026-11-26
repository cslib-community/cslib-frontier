/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.RedPaths.Basic
import Mathlib.Tactic.FinCases

/-!
# Checked red-path connectivity through substitution

Finite predecessor forests certify red-port connectivity in every corrected Robinson
parent's two-substitution block. Each row stores one edge to an earlier row, with its
crossing parity. The checks cover every live port, including the central base region;
the same forests certify the even east and north connectors. No search algorithm is
part of the logical interface.

## Main definitions

* `refinedPort`: side-sensitive port embedding through two substitutions.
* `sources`: new-cycle and inherited sources for local coverage.

## Main results

* `livePortPath`: live old ports reach their refined images
  with even crossing parity.
* `exists_boundedPath`: every live fine port is reached
  from the new cycle or an inherited live old port.
* `odd_base_exists_boundedPath`: every live port in the depth-four odd base has a
  bounded path from a cycle corner.
* `Path.refine`: arbitrary red paths preserve parity through
  two substitutions.

## References

The corrected construction is after [JeandelVanier2020], §§3.2–3.3, Figures 16–18
(manuscript pp. 26–28).
Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`, `RedShadeGraphCertificate`,
`RedShadeGraphLocalCoverage`, `RedShadeGraphRefinement`, `RedShadeGraphPathRefinement`,
`RedShadeGraphTranslation`, `RedShadeGraphCoarsening` and `CanonicalOddShadeBase`.
The predecessor compression is original; its finite input derives from that revision's
`RedShadeGraphPathWitnesses` (including `oddNodes`) and keeps every port and crossing
parity unchanged.
-/

public section
namespace Cslib.WangTile.Robinson

/-- The two exits of a quarter macrocell needing a connector. -/
private inductive ExitSide where
  | east | north
  deriving DecidableEq

private instance : Fintype ExitSide :=
  Fintype.ofList [.east, .north] (by intro side; cases side <;> simp)

/-- Constant grid with the specified parent tile. -/
@[expose] def coarseGrid (parent : Index) : Nat → Nat → Index := fun _ _ => parent

/-- The grid obtained by substituting a constant parent grid twice. -/
@[expose] def fineGrid (parent : Index) : Nat → Nat → Index :=
  iterateRefine 2 (coarseGrid parent)

/-- Two substitution steps depend only on the containing parent and local block coordinates. -/
theorem iterateRefine_two_local (grid : ℕ → ℕ → Index) (x y : ℕ) :
    iterateRefine 2 grid x y = fineGrid (grid (x / 4) (y / 4)) (x % 4) (y % 4) := by
  have coords (z : ℕ) : z / 2 / 2 = z / 4 ∧
      (z % 4) / 2 = z / 2 % 2 ∧ (z % 4) % 2 = z % 2 := by omega
  obtain ⟨hx₀, hx₁, hx₂⟩ := coords x
  obtain ⟨hy₀, hy₁, hy₂⟩ := coords y
  simp only [iterateRefine, refineIndexGrid, fineGrid, coarseGrid,
    hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, Nat.mod_mod]

/-- A live exit of the old southwest quarter block. -/
private def internalPort (side : ExitSide) (offset : Nat) : Port :=
  match side with
  | .east => ⟨1, offset, .east⟩
  | .north => ⟨offset, 1, .north⟩

/-- The corresponding exit on the boundary of the substituted macrocell. -/
private def externalPort (side : ExitSide) (offset : Nat) : Port :=
  match side with
  | .east => ⟨7, offset, .east⟩
  | .north => ⟨offset, 7, .north⟩

/-- Embed an old quarter coordinate into its macrocell's southwest two positions. -/
@[expose] def sparseCoordinate (coordinate : Nat) : Nat :=
  8 * (coordinate / 2) + coordinate % 2

/-- The sparse embedded old port, retaining its side. -/
@[expose] def sparsePort (port : Port) : Port :=
  ⟨sparseCoordinate port.x, sparseCoordinate port.y, port.side⟩

/-- All ports in the specified quarter rectangle. -/
@[expose] def portsIn (width height : Nat) : List Port :=
  (List.range height).flatMap fun y => (List.range width).flatMap fun x =>
    [⟨x, y, .west⟩, ⟨x, y, .east⟩, ⟨x, y, .south⟩, ⟨x, y, .north⟩]

/-- A port is listed in a rectangle exactly when both its coordinates are in bounds. -/
theorem mem_portsIn_iff {p : Port} {width height : Nat} :
    p ∈ portsIn width height ↔ PortInBounds p width height := by
  rcases p with ⟨px, py, _ | _ | _ | _⟩ <;>
    simp [portsIn, PortInBounds, and_comm]

/-- A strict bottom-side port of the cycle created in a depth-two block. -/
@[expose] def cycleSource : Port := ⟨4, 3, .west⟩

/-- The new cycle source and the sparse copies of every live old port. -/
@[expose] def sources (parent : Index) : List Port :=
  cycleSource :: ((portsIn 2 2).filter (portPresent (coarseGrid parent))).map sparsePort

namespace RedPathCertificate

private inductive Kind where
  | horizontalMatch | verticalMatch | horizontal | vertical
  | westNorth | westSouth | eastNorth | eastSouth | crossing
  deriving DecidableEq

private structure Move where
  x : Nat
  y : Nat
  kind : Kind
  reverse : Bool

private def decodePort (width code : Nat) : Port :=
  ⟨code / 4 % width, code / 4 / width,
    match code % 4 with | 0 => .west | 1 => .east | 2 => .south | _ => .north⟩

private def decodeMove (width code : Nat) : Move :=
  ⟨code / 2 / 9 % width, code / 2 / 9 / width,
    match code / 2 % 9 with
    | 0 => .horizontalMatch | 1 => .verticalMatch | 2 => .horizontal | 3 => .vertical
    | 4 => .westNorth | 5 => .westSouth | 6 => .eastNorth | 7 => .eastSouth | _ => .crossing,
    code % 2 == 1⟩

private def Move.baseFirst (m : Move) : Port :=
  ⟨m.x, m.y, match m.kind with
    | .horizontalMatch | .eastNorth | .eastSouth => .east
    | .verticalMatch => .north | .vertical => .south | _ => .west⟩

private def Move.baseSecond (m : Move) : Port :=
  match m.kind with
  | .horizontalMatch => ⟨m.x + 1, m.y, .west⟩
  | .verticalMatch => ⟨m.x, m.y + 1, .south⟩
  | .horizontal => ⟨m.x, m.y, .east⟩
  | .vertical | .westNorth | .eastNorth => ⟨m.x, m.y, .north⟩
  | .westSouth | .eastSouth | .crossing => ⟨m.x, m.y, .south⟩

private def Move.first (m : Move) : Port := if m.reverse then m.baseSecond else m.baseFirst
private def Move.second (m : Move) : Port := if m.reverse then m.baseFirst else m.baseSecond
private def Move.parity (m : Move) : Bool := m.kind == .crossing

private def Move.valid (grid : Nat → Nat → Index) (m : Move) : Bool :=
  let component := componentAt grid m.x m.y
  let q := quadrantAt m.x m.y
  match m.kind with
  | .horizontalMatch | .verticalMatch => true
  | .horizontal => hasHorizontal component q | .vertical => hasVertical component q
  | .westNorth => cornerWest component q && cornerNorth component q
  | .westSouth => cornerWest component q && cornerSouth component q
  | .eastNorth => cornerEast component q && cornerNorth component q
  | .eastSouth => cornerEast component q && cornerSouth component q
  | .crossing => hasHorizontal component q && hasVertical component q

private theorem Move.link {grid : Nat → Nat → Index} (m : Move)
    (h : m.valid grid = true) : Link grid m.first m.second m.parity := by
  rcases m with ⟨x, y, kind, reverse⟩
  have h0 : Link grid (Move.mk x y kind false).first (Move.mk x y kind false).second
      (Move.mk x y kind false).parity := by
    cases kind <;>
      simp only [Move.valid, Move.first, Move.second, Move.baseFirst, Move.baseSecond,
        Move.parity, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_self_eq_true] at h ⊢
    exacts [Link.horizontalMatch x y, Link.verticalMatch x y, Link.horizontal x y h,
      Link.vertical x y h, Link.westNorth x y h.1 h.2, Link.westSouth x y h.1 h.2,
      Link.eastNorth x y h.1 h.2, Link.eastSouth x y h.1 h.2, Link.crossing x y h.1 h.2]
  cases reverse
  · exact h0
  · exact h0.symm

/-- One predecessor edge in a finite red-path certificate. Port codes use row-major
coordinates with four sides in west/east/south/north order; move codes use row-major
coordinates, then one of the nine link kinds, then the reversal bit. -/
private structure Row where
  /-- Encoded endpoint of this row. -/
  port : Nat
  /-- Crossing parity of the path from the forest root. -/
  parity : Bool
  /-- Index of an earlier row whose endpoint starts the edge. -/
  predecessor : Nat
  /-- Encoded edge from the predecessor to this endpoint. -/
  move : Nat

/-- A predecessor forest whose encoded coordinates have the given row width. -/
private structure Forest (width : Nat) where
  /-- Encoded starting port common to all certified paths. -/
  root : Nat
  /-- Rows in predecessor order. -/
  rows : List Row

/-- The starting port obtained by decoding the forest's root. -/
private def Forest.rootPort {width : Nat} (f : Forest width) : Port :=
  decodePort width f.root

private def Forest.row {width : Nat} (f : Forest width) (i : Nat) : Row :=
  f.rows.getD i ⟨0, false, 0, 0⟩

private instance (p : Port) (w h : Nat) : Decidable (PortInBounds p w h) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Each row is either the root or a valid edge from an earlier row, and all ports
stay inside the square of the forest width. -/
private def Forest.Valid {width : Nat} (grid : Nat → Nat → Index) (f : Forest width) : Prop :=
  PortInBounds (decodePort width f.root) width width ∧
  ∀ i : Fin f.rows.length,
    let r := f.row i
    PortInBounds (decodePort width r.port) width width ∧
    ((r.port = f.root ∧ r.parity = false) ∨
      (r.predecessor < i.val ∧
       (decodeMove width r.move).valid grid = true ∧
       (decodeMove width r.move).first = decodePort width (f.row r.predecessor).port ∧
       (decodeMove width r.move).second = decodePort width r.port ∧
       r.parity = ((f.row r.predecessor).parity ^^ (decodeMove width r.move).parity)))

private instance {width : Nat} (grid : Nat → Nat → Index) (f : Forest width) :
    Decidable (f.Valid grid) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _ : Fin f.rows.length, _))

private theorem Forest.sound {width : Nat} {grid : Nat → Nat → Index} {f : Forest width}
    (valid : f.Valid grid) (i : Nat) (hi : i < f.rows.length) :
    BoundedPath grid width width (decodePort width f.root) (decodePort width (f.row i).port)
      (f.row i).parity := by
  obtain ⟨bounds, root | ⟨decreases, edge, first, second, parity⟩⟩ := valid.2 ⟨i, hi⟩
  · rcases root with ⟨hp, hb⟩
    rw [hp, hb]
    exact BoundedPath.refl _ valid.1
  · have predecessorBounds := (valid.2 ⟨(f.row i).predecessor, lt_trans decreases hi⟩).1
    have step := BoundedPath.ofLink ((decodeMove width (f.row i).move).link edge)
      (first.symm ▸ predecessorBounds) (second.symm ▸ bounds)
    rw [first, second] at step
    rw [parity]
    exact BoundedPath.trans (Forest.sound valid _ (lt_trans decreases hi)) step
termination_by i

private theorem Forest.sound_mem {width : Nat} {grid : Nat → Nat → Index} {f : Forest width}
    (valid : f.Valid grid) {r : Row} (hr : r ∈ f.rows) :
    BoundedPath grid width width (decodePort width f.root) (decodePort width r.port) r.parity := by
  obtain ⟨i, hi, equal⟩ := List.mem_iff_getElem.mp hr
  have rowEq : f.row i = r := by
    simp only [Forest.row, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some, equal]
  simpa only [rowEq] using Forest.sound valid i hi

-- Shared by all 104 parents: one predecessor per port, without repeated path tails.
private def forest (id : Fin 32) : Forest 8 :=
  match id.val with
  | 0 => ⟨37, [
      ⟨37, false, 0, 0⟩, ⟨40, false, 0, 162⟩, ⟨41, false, 1, 184⟩,
      ⟨44, false, 2, 180⟩, ⟨45, false, 3, 202⟩, ⟨48, false, 4, 198⟩,
      ⟨49, false, 5, 220⟩, ⟨52, false, 6, 216⟩, ⟨53, false, 7, 238⟩,
      ⟨56, false, 8, 234⟩, ⟨57, false, 9, 256⟩, ⟨60, false, 10, 252⟩,
      ⟨61, false, 11, 274⟩
    ]⟩
  | 1 => ⟨39, [
      ⟨39, false, 0, 0⟩, ⟨70, false, 0, 164⟩, ⟨71, false, 1, 312⟩,
      ⟨102, false, 2, 308⟩, ⟨103, false, 3, 456⟩, ⟨134, false, 4, 452⟩,
      ⟨135, false, 5, 600⟩, ⟨166, false, 6, 596⟩, ⟨167, false, 7, 744⟩,
      ⟨198, false, 8, 740⟩, ⟨199, false, 9, 888⟩, ⟨230, false, 10, 884⟩,
      ⟨231, false, 11, 1032⟩
    ]⟩
  | 2 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨142, false, 3, 488⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 6, 636⟩,
      ⟨123, false, 7, 548⟩, ⟨174, false, 8, 632⟩, ⟨154, false, 9, 542⟩,
      ⟨175, false, 10, 780⟩, ⟨155, false, 11, 690⟩, ⟨206, false, 12, 776⟩,
      ⟨186, false, 13, 686⟩, ⟨205, false, 14, 933⟩, ⟨184, true, 15, 845⟩,
      ⟨187, false, 15, 834⟩, ⟨208, false, 16, 918⟩, ⟨181, true, 17, 811⟩,
      ⟨185, true, 17, 832⟩, ⟨209, false, 19, 940⟩, ⟨218, false, 18, 830⟩,
      ⟨183, true, 20, 822⟩, ⟨188, true, 21, 828⟩, ⟨212, false, 22, 936⟩,
      ⟨216, false, 23, 983⟩, ⟨189, true, 25, 850⟩, ⟨213, false, 27, 955⟩,
      ⟨214, true, 24, 812⟩, ⟨215, true, 30, 960⟩, ⟨246, true, 31, 956⟩,
      ⟨247, true, 32, 1104⟩
    ]⟩
  | 3 => ⟨32, [
      ⟨32, false, 0, 0⟩
    ]⟩
  | 4 => ⟨35, [
      ⟨35, false, 0, 0⟩, ⟨66, false, 0, 146⟩, ⟨67, false, 1, 294⟩,
      ⟨98, false, 2, 290⟩, ⟨99, false, 3, 438⟩, ⟨130, false, 4, 434⟩,
      ⟨131, false, 5, 582⟩, ⟨162, false, 6, 578⟩, ⟨163, false, 7, 726⟩,
      ⟨194, false, 8, 722⟩, ⟨195, false, 9, 870⟩, ⟨226, false, 10, 866⟩,
      ⟨227, false, 11, 1014⟩
    ]⟩
  | 5 => ⟨5, [
      ⟨5, false, 0, 0⟩, ⟨8, false, 0, 18⟩, ⟨9, false, 1, 40⟩,
      ⟨12, false, 2, 36⟩, ⟨13, false, 3, 58⟩, ⟨16, false, 4, 54⟩,
      ⟨17, false, 5, 76⟩, ⟨20, false, 6, 72⟩, ⟨21, false, 7, 94⟩,
      ⟨24, false, 8, 90⟩, ⟨25, false, 9, 112⟩, ⟨28, false, 10, 108⟩,
      ⟨29, false, 11, 130⟩
    ]⟩
  | 6 => ⟨6, [
      ⟨6, false, 0, 0⟩
    ]⟩
  | 7 => ⟨0, [
      ⟨0, false, 0, 0⟩
    ]⟩
  | 8 => ⟨2, [
      ⟨2, false, 0, 0⟩
    ]⟩
  | 9 => ⟨39, [
      ⟨39, false, 0, 0⟩, ⟨70, false, 0, 164⟩, ⟨71, false, 1, 312⟩,
      ⟨102, false, 2, 308⟩, ⟨103, false, 3, 456⟩, ⟨134, false, 4, 452⟩,
      ⟨132, true, 5, 611⟩, ⟨135, false, 5, 600⟩, ⟨129, true, 6, 577⟩,
      ⟨166, false, 7, 596⟩, ⟨128, true, 8, 581⟩, ⟨167, false, 9, 744⟩,
      ⟨198, false, 11, 740⟩, ⟨199, false, 12, 888⟩, ⟨230, false, 13, 884⟩,
      ⟨231, false, 14, 1032⟩
    ]⟩
  | 10 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨114, true, 0, 520⟩, ⟨83, true, 3, 363⟩, ⟨111, false, 1, 498⟩,
      ⟨115, true, 3, 510⟩, ⟨116, false, 2, 504⟩, ⟨82, true, 4, 367⟩,
      ⟨117, false, 7, 526⟩, ⟨142, false, 5, 488⟩, ⟨146, true, 6, 506⟩,
      ⟨51, true, 8, 219⟩, ⟨120, false, 9, 522⟩, ⟨140, true, 10, 647⟩,
      ⟨143, false, 10, 636⟩, ⟨144, true, 11, 659⟩, ⟨50, true, 12, 223⟩,
      ⟨123, false, 13, 548⟩, ⟨137, true, 14, 613⟩, ⟨141, true, 16, 631⟩,
      ⟨174, false, 15, 632⟩, ⟨19, true, 17, 75⟩, ⟨136, true, 19, 617⟩,
      ⟨154, false, 18, 542⟩, ⟨175, false, 21, 780⟩, ⟨18, true, 22, 79⟩,
      ⟨133, true, 23, 595⟩, ⟨155, false, 24, 690⟩, ⟨206, false, 25, 776⟩,
      ⟨186, false, 28, 686⟩, ⟨205, false, 29, 933⟩, ⟨187, false, 30, 834⟩,
      ⟨208, false, 31, 918⟩, ⟨209, false, 33, 940⟩, ⟨218, false, 32, 830⟩,
      ⟨212, false, 34, 936⟩, ⟨216, false, 35, 983⟩, ⟨213, false, 37, 955⟩
    ]⟩
  | 11 => ⟨35, [
      ⟨35, false, 0, 0⟩, ⟨66, false, 0, 146⟩, ⟨67, false, 1, 294⟩,
      ⟨98, false, 2, 290⟩, ⟨99, false, 3, 438⟩, ⟨130, false, 4, 434⟩,
      ⟨128, true, 5, 593⟩, ⟨131, false, 5, 582⟩, ⟨129, true, 6, 580⟩,
      ⟨162, false, 7, 578⟩, ⟨163, false, 9, 726⟩, ⟨194, false, 10, 722⟩,
      ⟨195, false, 11, 870⟩, ⟨226, false, 12, 866⟩, ⟨227, false, 13, 1014⟩
    ]⟩
  | 12 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨114, true, 0, 520⟩, ⟨83, true, 3, 363⟩, ⟨111, false, 1, 498⟩,
      ⟨115, true, 3, 510⟩, ⟨116, false, 2, 504⟩, ⟨82, true, 4, 367⟩,
      ⟨117, false, 7, 526⟩, ⟨142, false, 5, 488⟩, ⟨146, true, 6, 506⟩,
      ⟨51, true, 8, 219⟩, ⟨120, false, 9, 522⟩, ⟨140, true, 10, 647⟩,
      ⟨143, false, 10, 636⟩, ⟨144, true, 11, 659⟩, ⟨50, true, 12, 223⟩,
      ⟨123, false, 13, 548⟩, ⟨137, true, 14, 613⟩, ⟨141, true, 16, 631⟩,
      ⟨174, false, 15, 632⟩, ⟨19, true, 17, 75⟩, ⟨136, true, 19, 617⟩,
      ⟨154, false, 18, 542⟩, ⟨175, false, 21, 780⟩, ⟨18, true, 22, 79⟩,
      ⟨133, true, 23, 595⟩, ⟨155, false, 24, 690⟩, ⟨206, false, 25, 776⟩,
      ⟨132, true, 27, 599⟩, ⟨186, false, 28, 686⟩, ⟨205, false, 29, 933⟩,
      ⟨187, false, 31, 834⟩, ⟨208, false, 32, 918⟩, ⟨209, false, 34, 940⟩,
      ⟨218, false, 33, 830⟩, ⟨212, false, 35, 936⟩, ⟨216, false, 36, 983⟩,
      ⟨213, false, 38, 955⟩
    ]⟩
  | 13 => ⟨5, [
      ⟨5, false, 0, 0⟩, ⟨8, false, 0, 18⟩, ⟨9, false, 1, 40⟩,
      ⟨12, false, 2, 36⟩, ⟨13, false, 3, 58⟩, ⟨16, false, 4, 54⟩,
      ⟨17, false, 5, 76⟩, ⟨18, true, 5, 88⟩, ⟨20, false, 6, 72⟩,
      ⟨21, false, 8, 94⟩, ⟨24, false, 9, 90⟩, ⟨25, false, 10, 112⟩,
      ⟨28, false, 11, 108⟩, ⟨29, false, 12, 130⟩
    ]⟩
  | 14 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨114, true, 0, 520⟩, ⟨83, true, 3, 363⟩, ⟨111, false, 1, 498⟩,
      ⟨115, true, 3, 510⟩, ⟨116, false, 2, 504⟩, ⟨82, true, 4, 367⟩,
      ⟨117, false, 7, 526⟩, ⟨142, false, 5, 488⟩, ⟨146, true, 6, 506⟩,
      ⟨51, true, 8, 219⟩, ⟨120, false, 9, 522⟩, ⟨140, true, 10, 647⟩,
      ⟨143, false, 10, 636⟩, ⟨144, true, 11, 659⟩, ⟨50, true, 12, 223⟩,
      ⟨123, false, 13, 548⟩, ⟨137, true, 14, 613⟩, ⟨141, true, 16, 631⟩,
      ⟨174, false, 15, 632⟩, ⟨19, true, 17, 75⟩, ⟨136, true, 19, 617⟩,
      ⟨154, false, 18, 542⟩, ⟨175, false, 21, 780⟩, ⟨133, true, 23, 595⟩,
      ⟨155, false, 24, 690⟩, ⟨206, false, 25, 776⟩, ⟨132, true, 26, 599⟩,
      ⟨186, false, 27, 686⟩, ⟨205, false, 28, 933⟩, ⟨129, true, 29, 577⟩,
      ⟨187, false, 30, 834⟩, ⟨208, false, 31, 918⟩, ⟨128, true, 32, 581⟩,
      ⟨209, false, 34, 940⟩, ⟨218, false, 33, 830⟩, ⟨212, false, 36, 936⟩,
      ⟨216, false, 37, 983⟩, ⟨213, false, 39, 955⟩
    ]⟩
  | 15 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨114, true, 0, 520⟩, ⟨83, true, 3, 363⟩, ⟨111, false, 1, 498⟩,
      ⟨115, true, 3, 510⟩, ⟨116, false, 2, 504⟩, ⟨82, true, 4, 367⟩,
      ⟨117, false, 7, 526⟩, ⟨142, false, 5, 488⟩, ⟨146, true, 6, 506⟩,
      ⟨51, true, 8, 219⟩, ⟨120, false, 9, 522⟩, ⟨140, true, 10, 647⟩,
      ⟨143, false, 10, 636⟩, ⟨144, true, 11, 659⟩, ⟨50, true, 12, 223⟩,
      ⟨123, false, 13, 548⟩, ⟨137, true, 14, 613⟩, ⟨141, true, 16, 631⟩,
      ⟨174, false, 15, 632⟩, ⟨19, true, 17, 75⟩, ⟨136, true, 19, 617⟩,
      ⟨154, false, 18, 542⟩, ⟨175, false, 21, 780⟩, ⟨18, true, 22, 79⟩,
      ⟨133, true, 23, 595⟩, ⟨155, false, 24, 690⟩, ⟨206, false, 25, 776⟩,
      ⟨132, true, 27, 599⟩, ⟨186, false, 28, 686⟩, ⟨205, false, 29, 933⟩,
      ⟨129, true, 30, 577⟩, ⟨187, false, 31, 834⟩, ⟨208, false, 32, 918⟩,
      ⟨128, true, 33, 581⟩, ⟨209, false, 35, 940⟩, ⟨218, false, 34, 830⟩,
      ⟨212, false, 37, 936⟩, ⟨216, false, 38, 983⟩, ⟨213, false, 40, 955⟩
    ]⟩
  | 16 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨142, false, 3, 488⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 6, 636⟩,
      ⟨123, false, 7, 548⟩, ⟨174, false, 8, 632⟩, ⟨154, false, 9, 542⟩,
      ⟨172, true, 10, 791⟩, ⟨175, false, 10, 780⟩, ⟨155, false, 11, 690⟩,
      ⟨169, true, 12, 757⟩, ⟨173, true, 12, 778⟩, ⟨206, false, 13, 776⟩,
      ⟨168, true, 15, 761⟩, ⟨176, true, 16, 774⟩, ⟨186, false, 14, 686⟩,
      ⟨205, false, 17, 933⟩, ⟨165, true, 18, 739⟩, ⟨179, true, 19, 800⟩,
      ⟨187, false, 20, 834⟩, ⟨208, false, 21, 918⟩, ⟨164, true, 22, 743⟩,
      ⟨209, false, 25, 940⟩, ⟨210, true, 25, 952⟩, ⟨218, false, 24, 830⟩,
      ⟨161, true, 26, 721⟩, ⟨211, true, 28, 942⟩, ⟨212, false, 27, 936⟩,
      ⟨216, false, 29, 983⟩, ⟨160, true, 30, 725⟩, ⟨213, false, 33, 955⟩,
      ⟨242, true, 31, 938⟩, ⟨243, true, 36, 1086⟩
    ]⟩
  | 17 => ⟨1, [
      ⟨1, false, 0, 0⟩
    ]⟩
  | 18 => ⟨4, [
      ⟨4, false, 0, 0⟩
    ]⟩
  | 19 => ⟨7, [
      ⟨7, false, 0, 0⟩
    ]⟩
  | 20 => ⟨38, [
      ⟨38, false, 0, 0⟩
    ]⟩
  | 21 => ⟨39, [
      ⟨39, false, 0, 0⟩, ⟨70, false, 0, 164⟩, ⟨71, false, 1, 312⟩,
      ⟨102, false, 2, 308⟩, ⟨103, false, 3, 456⟩, ⟨134, false, 4, 452⟩,
      ⟨135, false, 5, 600⟩, ⟨166, false, 6, 596⟩, ⟨164, true, 7, 755⟩,
      ⟨167, false, 7, 744⟩, ⟨161, true, 8, 721⟩, ⟨198, false, 9, 740⟩,
      ⟨160, true, 10, 725⟩, ⟨199, false, 11, 888⟩, ⟨230, false, 13, 884⟩,
      ⟨231, false, 14, 1032⟩
    ]⟩
  | 22 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨142, false, 3, 488⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 6, 636⟩,
      ⟨123, false, 7, 548⟩, ⟨174, false, 8, 632⟩, ⟨154, false, 9, 542⟩,
      ⟨172, true, 10, 791⟩, ⟨175, false, 10, 780⟩, ⟨155, false, 11, 690⟩,
      ⟨169, true, 12, 757⟩, ⟨173, true, 12, 778⟩, ⟨206, false, 13, 776⟩,
      ⟨168, true, 15, 761⟩, ⟨176, true, 16, 774⟩, ⟨186, false, 14, 686⟩,
      ⟨205, false, 17, 933⟩, ⟨165, true, 18, 739⟩, ⟨179, true, 19, 800⟩,
      ⟨187, false, 20, 834⟩, ⟨208, false, 21, 918⟩, ⟨209, false, 25, 940⟩,
      ⟨210, true, 25, 952⟩, ⟨218, false, 24, 830⟩, ⟨211, true, 27, 942⟩,
      ⟨212, false, 26, 936⟩, ⟨216, false, 28, 983⟩, ⟨213, false, 31, 955⟩,
      ⟨242, true, 29, 938⟩, ⟨243, true, 33, 1086⟩
    ]⟩
  | 23 => ⟨33, [
      ⟨33, false, 0, 0⟩
    ]⟩
  | 24 => ⟨36, [
      ⟨36, false, 0, 0⟩
    ]⟩
  | 25 => ⟨3, [
      ⟨3, false, 0, 0⟩
    ]⟩
  | 26 => ⟨34, [
      ⟨34, false, 0, 0⟩
    ]⟩
  | 27 => ⟨35, [
      ⟨35, false, 0, 0⟩, ⟨66, false, 0, 146⟩, ⟨67, false, 1, 294⟩,
      ⟨98, false, 2, 290⟩, ⟨99, false, 3, 438⟩, ⟨130, false, 4, 434⟩,
      ⟨131, false, 5, 582⟩, ⟨162, false, 6, 578⟩, ⟨160, true, 7, 737⟩,
      ⟨163, false, 7, 726⟩, ⟨161, true, 8, 724⟩, ⟨194, false, 9, 722⟩,
      ⟨195, false, 11, 870⟩, ⟨226, false, 12, 866⟩, ⟨227, false, 13, 1014⟩
    ]⟩
  | 28 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨142, false, 3, 488⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 6, 636⟩,
      ⟨123, false, 7, 548⟩, ⟨174, false, 8, 632⟩, ⟨154, false, 9, 542⟩,
      ⟨172, true, 10, 791⟩, ⟨175, false, 10, 780⟩, ⟨155, false, 11, 690⟩,
      ⟨169, true, 12, 757⟩, ⟨173, true, 12, 778⟩, ⟨206, false, 13, 776⟩,
      ⟨168, true, 15, 761⟩, ⟨176, true, 16, 774⟩, ⟨186, false, 14, 686⟩,
      ⟨205, false, 17, 933⟩, ⟨165, true, 18, 739⟩, ⟨179, true, 19, 800⟩,
      ⟨187, false, 20, 834⟩, ⟨208, false, 21, 918⟩, ⟨164, true, 22, 743⟩,
      ⟨209, false, 25, 940⟩, ⟨210, true, 25, 952⟩, ⟨218, false, 24, 830⟩,
      ⟨211, true, 28, 942⟩, ⟨212, false, 27, 936⟩, ⟨216, false, 29, 983⟩,
      ⟨213, false, 32, 955⟩, ⟨242, true, 30, 938⟩, ⟨243, true, 34, 1086⟩
    ]⟩
  | 29 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨118, true, 4, 538⟩, ⟨142, false, 3, 488⟩, ⟨87, true, 6, 381⟩,
      ⟨119, true, 6, 528⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 7, 636⟩,
      ⟨86, true, 8, 385⟩, ⟨123, false, 10, 548⟩, ⟨150, true, 9, 524⟩,
      ⟨174, false, 11, 632⟩, ⟨55, true, 12, 237⟩, ⟨149, true, 14, 681⟩,
      ⟨154, false, 13, 542⟩, ⟨175, false, 15, 780⟩, ⟨54, true, 16, 241⟩,
      ⟨152, true, 18, 701⟩, ⟨155, false, 18, 690⟩, ⟨206, false, 19, 776⟩,
      ⟨23, true, 20, 93⟩, ⟨153, true, 21, 688⟩, ⟨186, false, 22, 686⟩,
      ⟨205, false, 23, 933⟩, ⟨22, true, 24, 97⟩, ⟨156, true, 25, 684⟩,
      ⟨187, false, 26, 834⟩, ⟨208, false, 27, 918⟩, ⟨157, true, 29, 706⟩,
      ⟨209, false, 31, 940⟩, ⟨218, false, 30, 830⟩, ⟨212, false, 33, 936⟩,
      ⟨216, false, 34, 983⟩, ⟨213, false, 36, 955⟩
    ]⟩
  | 30 => ⟨5, [
      ⟨5, false, 0, 0⟩, ⟨8, false, 0, 18⟩, ⟨9, false, 1, 40⟩,
      ⟨12, false, 2, 36⟩, ⟨13, false, 3, 58⟩, ⟨16, false, 4, 54⟩,
      ⟨17, false, 5, 76⟩, ⟨20, false, 6, 72⟩, ⟨21, false, 7, 94⟩,
      ⟨22, true, 7, 106⟩, ⟨24, false, 8, 90⟩, ⟨25, false, 10, 112⟩,
      ⟨28, false, 11, 108⟩, ⟨29, false, 12, 130⟩
    ]⟩
  | _ => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨118, true, 4, 538⟩, ⟨142, false, 3, 488⟩, ⟨87, true, 6, 381⟩,
      ⟨119, true, 6, 528⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 7, 636⟩,
      ⟨86, true, 8, 385⟩, ⟨123, false, 10, 548⟩, ⟨150, true, 9, 524⟩,
      ⟨174, false, 11, 632⟩, ⟨55, true, 12, 237⟩, ⟨149, true, 14, 681⟩,
      ⟨154, false, 13, 542⟩, ⟨175, false, 15, 780⟩, ⟨54, true, 16, 241⟩,
      ⟨152, true, 18, 701⟩, ⟨155, false, 18, 690⟩, ⟨206, false, 19, 776⟩,
      ⟨23, true, 20, 93⟩, ⟨153, true, 21, 688⟩, ⟨186, false, 22, 686⟩,
      ⟨205, false, 23, 933⟩, ⟨156, true, 25, 684⟩, ⟨187, false, 26, 834⟩,
      ⟨208, false, 27, 918⟩, ⟨157, true, 28, 706⟩, ⟨209, false, 30, 940⟩,
      ⟨218, false, 29, 830⟩, ⟨212, false, 32, 936⟩, ⟨216, false, 33, 983⟩,
      ⟨213, false, 35, 955⟩
    ]⟩

private def selected (parent : Index) : List (Fin 32) :=
  match parent.val with
  | 0 => [0, 1, 2]
  | 1 => [3, 4, 2]
  | 2 => [5, 6, 2]
  | 3 => [7, 8, 2]
  | 4 => [0, 9, 10]
  | 5 => [3, 11, 12]
  | 6 => [13, 6, 14]
  | 7 => [7, 8, 15]
  | 8 | 9 | 20 | 21 | 24 | 25 | 28 | 29 => [16]
  | 10 | 11 | 26 | 27 => [7, 17, 18, 5, 16]
  | 12 | 14 => [6, 19, 20, 21, 22]
  | 13 => [6, 19, 3, 23, 24, 0, 20, 21, 22]
  | 15 => [7, 17, 18, 5, 6, 19, 20, 21, 22]
  | 16 | 18 => [8, 25, 26, 27, 28]
  | 17 => [8, 25, 3, 23, 26, 27, 24, 0, 28]
  | 19 => [7, 17, 8, 25, 18, 5, 26, 27, 28]
  | 22 | 23 | 30 | 31 => [3, 23, 24, 0, 16]
  | 32 | 33 | 44 | 45 | 48 | 49 | 52 | 53 | 92 | 93 | 95 | 96 | 98 | 99 | 101 | 102 => [2]
  | 36 | 38 | 80 | 81 | 83 | 84 => [6, 19, 20, 1, 2]
  | 37 | 82 => [6, 19, 3, 23, 24, 0, 20, 1, 2]
  | 39 | 85 => [7, 17, 18, 5, 6, 19, 20, 1, 2]
  | 40 | 42 | 86 | 87 | 89 | 90 => [8, 25, 26, 4, 2]
  | 41 | 88 => [8, 25, 3, 23, 26, 4, 24, 0, 2]
  | 43 | 91 => [7, 17, 8, 25, 18, 5, 26, 4, 2]
  | 46 | 47 | 54 | 55 | 94 | 100 => [3, 23, 24, 0, 2]
  | 56 | 57 | 59 | 60 => [6, 19, 20, 1, 29]
  | 58 => [6, 19, 3, 23, 24, 0, 20, 1, 29]
  | 61 => [7, 17, 18, 30, 6, 19, 20, 1, 31]
  | 62 | 63 | 65 | 66 => [8, 25, 26, 4, 29]
  | 64 => [8, 25, 3, 23, 26, 4, 24, 0, 29]
  | 67 => [7, 17, 8, 25, 18, 30, 26, 4, 31]
  | 68 | 69 | 71 | 72 | 74 | 75 | 77 | 78 => [29]
  | 70 | 76 => [3, 23, 24, 0, 29]
  | 73 | 79 => [7, 17, 18, 30, 31]
  | 34 | 35 | 50 | 51 | 97 | _ => [7, 17, 18, 5, 2]

/-- Whether one row of the forest ends at the target port. -/
private def Forest.reaches {width : Nat} (f : Forest width) (target : Port) : Bool :=
  f.rows.any fun r => decide (decodePort width r.port = target)

private def connects (f : Forest 8) (start finish : Port) : Bool :=
  decide (decodePort 8 f.root = start) &&
    f.rows.any fun r => decide (decodePort 8 r.port = finish ∧ r.parity = false)

private def Verified (parent : Index) : Prop :=
  (∀ id ∈ selected parent,
    (forest id).Valid (fineGrid parent) ∧ decodePort 8 (forest id).root ∈ sources parent) ∧
  (∀ x y : Fin 8, ∀ s : Side,
    portPresent (fineGrid parent) ⟨x, y, s⟩ = true →
    ((selected parent).any fun id => Forest.reaches (forest id) ⟨x, y, s⟩) = true) ∧
  (∀ exit : ExitSide, ∀ offset : Fin 2,
    portPresent (coarseGrid parent) (internalPort exit offset) = true →
    ((selected parent).any fun id =>
      connects (forest id) (internalPort exit offset) (externalPort exit offset)) = true)

private instance (parent : Index) : Decidable (Verified parent) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private theorem verified0 : ∀ i : Fin 13, Verified ⟨0 + i.val, by omega⟩ := by
  decide +kernel
private theorem verified1 : ∀ i : Fin 13, Verified ⟨13 + i.val, by omega⟩ := by
  decide +kernel
private theorem verified2 : ∀ i : Fin 13, Verified ⟨26 + i.val, by omega⟩ := by
  decide +kernel
private theorem verified3 : ∀ i : Fin 13, Verified ⟨39 + i.val, by omega⟩ := by
  decide +kernel
private theorem verified4 : ∀ i : Fin 13, Verified ⟨52 + i.val, by omega⟩ := by
  decide +kernel
private theorem verified5 : ∀ i : Fin 13, Verified ⟨65 + i.val, by omega⟩ := by
  decide +kernel
private theorem verified6 : ∀ i : Fin 13, Verified ⟨78 + i.val, by omega⟩ := by
  decide +kernel
private theorem verified7 : ∀ i : Fin 13, Verified ⟨91 + i.val, by omega⟩ := by
  decide +kernel

private theorem verified (parent : Index) : Verified parent := by
  have key : ∀ k : Fin 8, ∀ i : Fin 13, Verified ⟨13 * k.val + i.val, by omega⟩ := by
    intro k
    fin_cases k
    exacts [verified0, verified1, verified2, verified3, verified4, verified5, verified6, verified7]
  have e : (⟨13 * (parent.val / 13) + parent.val % 13, by omega⟩ : Index) = parent :=
    Fin.ext (Nat.div_add_mod _ _)
  exact e ▸ key ⟨parent.val / 13, by omega⟩ ⟨parent.val % 13, Nat.mod_lt _ (by decide)⟩

/-- A valid forest that reaches a port supplies a bounded red path with some parity. -/
private theorem Forest.reaches_sound {width : Nat} {grid : Nat → Nat → Index} {f : Forest width}
    (valid : f.Valid grid) {target : Port} (h : f.reaches target = true) :
    ∃ parity, BoundedPath grid width width f.rootPort target parity := by
  obtain ⟨r, hr, eq⟩ := List.any_eq_true.mp h
  have targetEq : decodePort width r.port = target := of_decide_eq_true eq
  exact ⟨r.parity, targetEq ▸ Forest.sound_mem valid hr⟩

private theorem connects_sound {grid : Nat → Nat → Index} {f : Forest 8}
    (valid : f.Valid grid) {start finish : Port} (h : connects f start finish = true) :
    BoundedPath grid 8 8 start finish false := by
  obtain ⟨hroot, hnode⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨r, hr, hend⟩ := List.any_eq_true.mp hnode
  obtain ⟨targetEq, parityEq⟩ := of_decide_eq_true hend
  simpa only [of_decide_eq_true hroot, targetEq, parityEq] using Forest.sound_mem valid hr

end RedPathCertificate
open RedPathCertificate

/-- Every live old east or north port reaches its macrocell boundary evenly,
with every intermediate port inside the `8 × 8` quarter block. -/
private theorem boundedConnectorPath (parent : Index) (exit : ExitSide)
    {offset : Nat} (hoffset : offset < 2)
    (present : portPresent (coarseGrid parent) (internalPort exit offset) = true) :
    BoundedPath (fineGrid parent) 8 8 (internalPort exit offset)
      (externalPort exit offset) false := by
  obtain ⟨id, hid, h⟩ :=
    List.any_eq_true.mp ((verified parent).2.2 exit ⟨offset, hoffset⟩ present)
  exact connects_sound ((verified parent).1 id hid).1 h

open RedPathCertificate

/-- Every live port in a two-substitution block has a bounded path from the
new cycle or an inherited live old port. -/
theorem exists_boundedPath (parent : Index) {target : Port}
    (mem : target ∈ portsIn 8 8)
    (present : portPresent (fineGrid parent) target = true) :
    ∃ source ∈ sources parent, ∃ parity,
      BoundedPath (fineGrid parent) 8 8 source target parity := by
  obtain ⟨hx, hy⟩ := mem_portsIn_iff.mp mem
  have accepted := (verified parent).2.1 ⟨target.x, hx⟩ ⟨target.y, hy⟩ target.side
  obtain ⟨id, hid, hreach⟩ := List.any_eq_true.mp (accepted present)
  obtain ⟨valid, hsource⟩ := (verified parent).1 id hid
  exact ⟨_, hsource, Forest.reaches_sound valid hreach⟩

private theorem baseChecked : ∀ x y : Fin 4, ∀ s : Side,
    portPresent (fineGrid 0) ⟨2 + x.val, 2 + y.val, s⟩ = true →
    Forest.reaches (forest 2) ⟨2 + x.val, 2 + y.val, s⟩ = true := by decide

/-- Every live port in the central `4 × 4` region of parent zero's block
belongs to the newly created cycle component. -/
theorem base_exists_boundedPath {target : Port}
    (west : 2 ≤ target.x) (east : target.x < 6)
    (south : 2 ≤ target.y) (north : target.y < 6)
    (present : portPresent (fineGrid 0) target = true) :
    ∃ parity, BoundedPath (fineGrid 0) 8 8 cycleSource target parity := by
  rcases target with ⟨tx, ty, ts⟩
  dsimp only at *
  have h := baseChecked ⟨tx - 2, by omega⟩ ⟨ty - 2, by omega⟩ ts
  rw [Nat.add_sub_of_le west, Nat.add_sub_of_le south] at h
  exact Forest.reaches_sound ((verified 0).1 2 (by decide)).1 (h present)

private abbrev oddGrid := iterateRefine 4 (fun _ _ => (0 : Index))

private def oddForests : List (RedPathCertificate.Forest 16) := [
  ⟨341, [
    ⟨341, false, 0, 0⟩, ⟨344, false, 0, 1530⟩, ⟨346, true, 1, 1564⟩,
    ⟨283, true, 2, 1263⟩, ⟨282, true, 3, 1267⟩, ⟨343, false, 0, 1542⟩,
    ⟨345, false, 1, 1552⟩, ⟨347, true, 2, 1554⟩, ⟨348, false, 6, 1548⟩,
    ⟨349, false, 8, 1570⟩, ⟨352, false, 9, 1566⟩, ⟨353, false, 10, 1588⟩,
    ⟨406, false, 5, 1532⟩, ⟨404, true, 12, 1835⟩, ⟨401, true, 13, 1801⟩,
    ⟨400, true, 14, 1805⟩, ⟨405, true, 13, 1822⟩, ⟨407, false, 12, 1824⟩,
    ⟨410, true, 7, 1550⟩, ⟨408, true, 18, 1847⟩, ⟨470, false, 17, 1820⟩,
    ⟨471, false, 20, 2112⟩, ⟨534, false, 21, 2108⟩, ⟨535, false, 22, 2400⟩
  ]⟩,
  ⟨368, [
    ⟨368, false, 0, 0⟩, ⟨365, false, 0, 1639⟩, ⟨364, false, 1, 1643⟩,
    ⟨366, true, 2, 1654⟩, ⟨303, true, 3, 1353⟩, ⟨302, true, 4, 1357⟩,
    ⟨361, false, 2, 1621⟩, ⟨360, false, 6, 1625⟩, ⟨357, false, 7, 1603⟩,
    ⟨356, false, 8, 1607⟩, ⟨367, true, 3, 1644⟩, ⟨371, false, 0, 1664⟩,
    ⟨434, false, 11, 1658⟩, ⟨432, true, 12, 1961⟩, ⟨429, true, 13, 1927⟩,
    ⟨430, true, 14, 1940⟩
  ]⟩,
  ⟨816, [
    ⟨816, false, 0, 0⟩, ⟨818, false, 0, 3682⟩, ⟨755, false, 1, 3387⟩,
    ⟨754, false, 2, 3391⟩, ⟨691, false, 3, 3099⟩, ⟨690, false, 4, 3103⟩,
    ⟨627, false, 5, 2811⟩, ⟨626, false, 6, 2815⟩, ⟨624, true, 7, 2825⟩,
    ⟨621, true, 8, 2791⟩, ⟨620, true, 9, 2795⟩, ⟨617, true, 10, 2773⟩,
    ⟨616, true, 11, 2777⟩, ⟨613, true, 12, 2755⟩, ⟨813, false, 0, 3655⟩,
    ⟨812, false, 14, 3659⟩, ⟨809, false, 15, 3637⟩, ⟨808, false, 16, 3641⟩,
    ⟨805, false, 17, 3619⟩, ⟨804, false, 18, 3623⟩, ⟨806, true, 19, 3634⟩,
    ⟨743, true, 20, 3333⟩, ⟨742, true, 21, 3337⟩, ⟨679, true, 22, 3045⟩,
    ⟨678, true, 23, 3049⟩, ⟨615, true, 24, 2757⟩, ⟨752, true, 3, 3401⟩,
    ⟨749, true, 26, 3367⟩, ⟨814, true, 15, 3670⟩, ⟨751, true, 28, 3369⟩
  ]⟩,
  ⟨789, [
    ⟨789, false, 0, 0⟩, ⟨790, false, 0, 3560⟩, ⟨727, false, 1, 3261⟩,
    ⟨726, false, 2, 3265⟩, ⟨663, false, 3, 2973⟩, ⟨662, false, 4, 2977⟩,
    ⟨599, false, 5, 2685⟩, ⟨598, false, 6, 2689⟩, ⟨724, true, 3, 3275⟩,
    ⟨721, true, 8, 3241⟩, ⟨720, true, 9, 3245⟩, ⟨792, false, 0, 3546⟩,
    ⟨794, true, 11, 3580⟩, ⟨731, true, 12, 3279⟩, ⟨728, true, 13, 3285⟩,
    ⟨725, true, 14, 3259⟩
  ]⟩
]

private theorem oddChecked : ∀ forest ∈ oddForests, forest.Valid oddGrid ∧
    forest.rootPort ∈ ([⟨5, 5, .east⟩, ⟨12, 5, .west⟩,
      ⟨12, 12, .west⟩, ⟨5, 12, .east⟩] : List Port) := by
  decide +kernel

private theorem oddCovers : ∀ x y : Fin 8, ∀ s : Side,
    portPresent oddGrid ⟨4 + x.val, 4 + y.val, s⟩ = true →
      (oddForests.any fun forest => forest.reaches ⟨4 + x.val, 4 + y.val, s⟩) = true := by
  decide +kernel

/-- Every live port in the odd root's central square has a bounded path from a root corner.
This is the finite base case of the odd-phase shade comparison, after lean-wang's
`CanonicalOddShadeBase.exists_boundedPath` at revision `64268a3`. -/
theorem odd_base_exists_boundedPath {target : Port}
    (west : 4 ≤ target.x) (east : target.x < 12)
    (south : 4 ≤ target.y) (north : target.y < 12)
    (present : portPresent (iterateRefine 4 (fun _ _ => (0 : Index))) target = true) :
    ∃ source parity,
      source ∈ ([⟨5, 5, .east⟩, ⟨12, 5, .west⟩, ⟨12, 12, .west⟩, ⟨5, 12, .east⟩] : List Port) ∧
      BoundedPath (iterateRefine 4 (fun _ _ => (0 : Index))) 16 16 source target parity := by
  rcases target with ⟨tx, ty, ts⟩
  dsimp only at *
  have h := oddCovers ⟨tx - 4, by omega⟩ ⟨ty - 4, by omega⟩ ts
  rw [Nat.add_sub_of_le west, Nat.add_sub_of_le south] at h
  obtain ⟨forest, mem, reached⟩ := List.any_eq_true.mp (h present)
  obtain ⟨valid, source⟩ := oddChecked forest mem
  obtain ⟨parity, path⟩ := Forest.reaches_sound valid reached
  exact ⟨forest.rootPort, parity, source, path⟩

/-- The two possible origins of a local coverage path. -/
theorem source_cases {parent : Index} {source : Port} (h : source ∈ sources parent) :
    source = cycleSource ∨ ∃ old ∈ portsIn 2 2,
      portPresent (coarseGrid parent) old = true ∧ source = sparsePort old := by
  simp only [sources, List.mem_cons, List.mem_map, List.mem_filter] at h
  exact h.imp_right fun ⟨old, ⟨mem, live⟩, eq⟩ => ⟨old, mem, live, eq.symm⟩

/-- Translate a quarter port without changing its side. -/
@[expose] def translatePort (port : Port) (offsetX offsetY : Nat) : Port :=
  ⟨offsetX + port.x, offsetY + port.y, port.side⟩

private theorem link_translate
    {grid other : Nat → Nat → Index} {width height offsetX offsetY : Nat}
    (hx : offsetX % 2 = 0) (hy : offsetY % 2 = 0)
    (componentsEq : ∀ x y, x < width → y < height →
      componentAt grid x y = componentAt other (offsetX + x) (offsetY + y))
    {first second : Port} {parity : Bool}
    (link : Link grid first second parity)
    (hfirst : PortInBounds first width height) (hsecond : PortInBounds second width height) :
    Link other (translatePort first offsetX offsetY)
      (translatePort second offsetX offsetY) parity := by
  have quadrant (x y) : quadrantAt (offsetX + x) (offsetY + y) = quadrantAt x y := by
    simp [quadrantAt, Nat.add_mod, hx, hy]
  induction link
  case horizontalMatch x y =>
    simpa only [translatePort, Nat.add_assoc] using
      Link.horizontalMatch (indexGrid := other) (offsetX + x) (offsetY + y)
  case verticalMatch x y =>
    simpa only [translatePort, Nat.add_assoc] using
      Link.verticalMatch (indexGrid := other) (offsetX + x) (offsetY + y)
  case symm _ ih => exact Link.symm (ih hsecond hfirst)
  all_goals constructor! <;> rwa [← componentsEq _ _ hfirst.1 hfirst.2, quadrant]

/-- Transport a bounded path to any even translate with the same local components. -/
theorem boundedPath_translate
    {grid other : Nat → Nat → Index} {width height offsetX offsetY : Nat}
    (hx : offsetX % 2 = 0) (hy : offsetY % 2 = 0)
    (componentsEq : ∀ x y, x < width → y < height →
      componentAt grid x y = componentAt other (offsetX + x) (offsetY + y))
    {first second : Port} {parity : Bool}
    (path : BoundedPath grid width height first second parity) :
    Path other (translatePort first offsetX offsetY)
      (translatePort second offsetX offsetY) parity := by
  induction path with
  | refl _ _ => exact .refl _
  | ofLink link hfirst hsecond =>
    exact .ofLink (link_translate hx hy componentsEq link hfirst hsecond)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- A twice-substituted macrocell depends only on its old parent tile. -/
theorem componentAt_two_block (grid : Nat → Nat → Index) (bx by₀ x y : Nat)
    (hx : x < 8) (hy : y < 8) :
    componentAt (iterateRefine 2 grid) (8 * bx + x) (8 * by₀ + y) =
      componentAt (fineGrid (grid bx by₀)) x y := by
  have coords (b z : Nat) (hz : z < 8) :
      (8 * b + z) / 2 / 2 / 2 = b ∧
      (8 * b + z) / 2 % 2 = z / 2 % 2 ∧
      (8 * b + z) / 2 / 2 % 2 = z / 2 / 2 % 2 := by omega
  obtain ⟨hx₀, hx₁, hx₂⟩ := coords bx x hx
  obtain ⟨hy₀, hy₁, hy₂⟩ := coords by₀ y hy
  simp only [fineGrid, coarseGrid, componentAt, iterateRefine, refineIndexGrid,
    hx₀, hx₁, hx₂, hy₀, hy₁, hy₂]

/-- A checked local route transplanted into the corresponding arbitrary macrocell. -/
theorem boundedPath_two_block (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {first target : Port} {parity : Bool}
    (path : BoundedPath (fineGrid (grid blockX blockY)) 8 8 first target parity) :
    Path (iterateRefine 2 grid)
      (translatePort first (8 * blockX) (8 * blockY))
      (translatePort target (8 * blockX) (8 * blockY)) parity :=
  boundedPath_translate (by omega) (by omega)
    (fun x y hx hy => (componentAt_two_block grid blockX blockY x y hx hy).symm) path

private theorem southwest_component (parent : Index) :
    ∀ x y : Fin 2,
      componentAt (fineGrid parent) x y = componentAt (coarseGrid parent) x y := by
  intro x y
  simpa [indexThick, fineGrid, coarseGrid, componentAt, iterateRefine, refineIndexGrid,
    Nat.div_eq_of_lt x.isLt, Nat.div_eq_of_lt y.isLt, Nat.zero_div, Nat.zero_mod] using
    (childBlock_thick_southwest (childBlock parent 0 0)).trans
      (childBlock_thick_southwest parent)

/-- The sparse old quarters retain their exact thick component. -/
theorem componentAt_iterateRefine_two_sparse (grid : Nat → Nat → Index) (x y : Nat) :
    componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y) =
      componentAt grid x y := by
  exact (componentAt_two_block grid (x / 2) (y / 2) (x % 2) (y % 2) (by omega)
    (by omega)).trans (southwest_component (grid (x / 2) (y / 2))
      ⟨x % 2, by omega⟩ ⟨y % 2, by omega⟩)

private theorem quadrantAt_sparse (x y : Nat) :
    quadrantAt (sparseCoordinate x) (sparseCoordinate y) = quadrantAt x y := by
  simp [quadrantAt, sparseCoordinate, Nat.add_mod, Nat.mul_mod]

/-- An east/north port is moved to the macrocell boundary when it exits an old tile. -/
@[expose] def exitCoordinate (coordinate : Nat) : Nat :=
  if coordinate % 2 = 1 then 8 * (coordinate / 2) + 7 else sparseCoordinate coordinate

/-- Side-sensitive refinement: west/south stay sparse, east/north reach the block boundary. -/
@[expose] def refinedPort (port : Port) : Port :=
  match port.side with
  | .east => ⟨exitCoordinate port.x, sparseCoordinate port.y, .east⟩
  | .north => ⟨sparseCoordinate port.x, exitCoordinate port.y, .north⟩
  | .west | .south => sparsePort port

private theorem exitCoordinate_succ (coordinate : Nat) :
    exitCoordinate coordinate + 1 = sparseCoordinate (coordinate + 1) := by
  unfold exitCoordinate sparseCoordinate
  split <;> omega

/-- Port incidence depends only on the containing tile and its local quarter. -/
theorem portPresent_local (grid : Nat → Nat → Index) (port : Port) :
    portPresent (coarseGrid (grid (port.x / 2) (port.y / 2)))
      ⟨port.x % 2, port.y % 2, port.side⟩ = portPresent grid port := by
  cases port with
  | mk x y s =>
    cases s <;> simp [portPresent, componentAt, coarseGrid, quadrantAt]

private theorem local_refinedPort_present (parent : Index) (x y : Fin 2) (s : Side) :
    portPresent (fineGrid parent) (refinedPort ⟨x, y, s⟩) =
      portPresent (coarseGrid parent) ⟨x, y, s⟩ := by
  cases s <;> fin_cases x <;> fin_cases y <;> revert parent <;> decide

/-- Port incidence is preserved when a bounded local block is embedded in a refined grid. -/
theorem portPresent_two_block (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (port : Port) (hx : port.x < 8) (hy : port.y < 8) :
    portPresent (fineGrid (grid blockX blockY)) port =
      portPresent (iterateRefine 2 grid)
        (translatePort port (8 * blockX) (8 * blockY)) := by
  have quadrant : quadrantAt (8 * blockX + port.x) (8 * blockY + port.y) =
      quadrantAt port.x port.y := by simp [quadrantAt, Nat.add_mod, Nat.mul_mod]
  cases hs : port.side <;> simp only [portPresent, translatePort, hs] <;>
    rw [componentAt_two_block grid blockX blockY port.x port.y hx hy, quadrant]

/-- The side-sensitive refined image carries a red wire exactly when the old port does. -/
theorem refinedPort_present (grid : Nat → Nat → Index) (port : Port) :
    portPresent (iterateRefine 2 grid) (refinedPort port) = portPresent grid port := by
  let x : Fin 2 := ⟨port.x % 2, Nat.mod_lt _ (by decide)⟩
  let y : Fin 2 := ⟨port.y % 2, Nat.mod_lt _ (by decide)⟩
  let oldPort : Port := ⟨x, y, port.side⟩
  have localBounds (i j : Fin 2) (s : Side) : PortInBounds (refinedPort ⟨i, j, s⟩) 8 8 := by
    cases s <;> fin_cases i <;> fin_cases j <;> unfold PortInBounds <;> decide
  have image : refinedPort port =
      translatePort (refinedPort oldPort) (8 * (port.x / 2)) (8 * (port.y / 2)) := by
    have hx : port.x % 2 / 2 = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
    have hy : port.y % 2 / 2 = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
    cases hs : port.side <;>
      simp [refinedPort, sparsePort, exitCoordinate, sparseCoordinate,
        translatePort, oldPort, x, y, hs, hx, hy, apply_ite]
  rw [image, ← portPresent_two_block grid (port.x / 2) (port.y / 2)
    (refinedPort oldPort) (localBounds x y port.side).1 (localBounds x y port.side).2,
    local_refinedPort_present (grid (port.x / 2) (port.y / 2)) x y port.side]
  exact portPresent_local grid port

/-- A live old port reaches its side-sensitive refined image with even parity. -/
theorem livePortPath (grid : Nat → Nat → Index) (port : Port)
    (live : portPresent grid port = true) :
    Path (iterateRefine 2 grid) (sparsePort port) (refinedPort port) false := by
  cases hs : port.side with
  | west | south => simpa only [refinedPort, hs] using Path.refl (sparsePort port)
  | east =>
    by_cases hx : port.x % 2 = 1
    · have present : portPresent (coarseGrid (grid (port.x / 2) (port.y / 2)))
        (internalPort .east (port.y % 2)) = true := by
        simpa only [internalPort, hs, hx] using (portPresent_local grid port).trans live
      simpa [sparsePort, refinedPort, hs, exitCoordinate, hx, internalPort, externalPort,
        translatePort, sparseCoordinate] using boundedPath_two_block grid (port.x / 2)
          (port.y / 2) (boundedConnectorPath _ .east (by omega) present)
    · simpa [refinedPort, hs, exitCoordinate, hx, sparsePort]
        using Path.refl (sparsePort port)
  | north =>
    by_cases hy : port.y % 2 = 1
    · have present : portPresent (coarseGrid (grid (port.x / 2) (port.y / 2)))
        (internalPort .north (port.x % 2)) = true := by
        simpa only [internalPort, hs, hy] using (portPresent_local grid port).trans live
      simpa [sparsePort, refinedPort, hs, exitCoordinate, hy, internalPort, externalPort,
        translatePort, sparseCoordinate] using boundedPath_two_block grid (port.x / 2)
          (port.y / 2) (boundedConnectorPath _ .north (by omega) present)
    · simpa [refinedPort, hs, exitCoordinate, hy, sparsePort]
        using Path.refl (sparsePort port)

private theorem path_of_sparseLink {grid : Nat → Nat → Index} {first second : Port}
    {parity : Bool} (hfirst : portPresent grid first = true)
    (hsecond : portPresent grid second = true)
    (link : Link (iterateRefine 2 grid) (sparsePort first) (sparsePort second) parity) :
    Path (iterateRefine 2 grid) (refinedPort first) (refinedPort second) parity := by
  simpa only [Bool.false_xor, Bool.xor_false] using
    Path.trans (livePortPath grid first hfirst).symm
      (Path.trans (.ofLink link) (livePortPath grid second hsecond))

/-- Every coarse link refines to a fine path with the same crossing parity. -/
theorem Link.refine {grid : Nat → Nat → Index} {first second : Port} {parity : Bool}
    (link : Link grid first second parity) :
    Path (iterateRefine 2 grid) (refinedPort first) (refinedPort second) parity := by
  induction link
  case horizontalMatch x y =>
    simpa only [refinedPort, sparsePort, exitCoordinate_succ] using
      Path.ofLink (Link.horizontalMatch (indexGrid := iterateRefine 2 grid)
        (exitCoordinate x) (sparseCoordinate y))
  case verticalMatch x y =>
    simpa only [refinedPort, sparsePort, exitCoordinate_succ] using
      Path.ofLink (Link.verticalMatch (indexGrid := iterateRefine 2 grid)
        (sparseCoordinate x) (exitCoordinate y))
  case symm _ ih => exact ih.symm
  all_goals
    apply path_of_sparseLink (by simp [portPresent, hasWest, hasEast, hasSouth, *])
      (by simp [portPresent, hasEast, hasSouth, hasNorth, *])
    constructor! <;>
      (simp only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse]; assumption)

/-- Two substitutions preserve the crossing parity of every red path. -/
theorem Path.refine {grid : Nat → Nat → Index} {first second : Port} {parity : Bool}
    (path : Path grid first second parity) :
    Path (iterateRefine 2 grid) (refinedPort first) (refinedPort second) parity := by
  induction path with
  | refl _ => exact .refl _
  | ofLink link => exact Link.refine link
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

end Cslib.WangTile.Robinson
