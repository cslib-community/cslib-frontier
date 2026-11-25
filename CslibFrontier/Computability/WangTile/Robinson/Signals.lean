/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Shading.Basic
public import CslibFrontier.Computability.WangTile.Routing
public import CslibFrontier.Computability.WangTile.Robinson.Hierarchy
import Mathlib.Tactic.FinCases

/-!
# The shaded Robinson signal scaffold

Directed obstruction signals pass unchanged between light borders. At a light border the outer
edge carries a signal and the inner edge may absorb one. Dark wires do not constrain signals.
Clear horizontal and vertical edges determine which payload directions the scaffold carries;
the clear northeast quarter of index zero additionally marks a seeded crossing.

## Main definitions

* `flowAllowed`: the common one-dimensional transmission and border rule.
* `ShadedSite`: a quarter with a shade state and an obstruction state.
* `scaffold`: the finite shaded Robinson scaffold with its routing decoder.
* `DecodedPlane`: the semantic sites of an ordinary scaffold plane.
* `QuarterPlane.regroup`: exact parent regrouping of any matching quarter plane.

## Main results

* `DecodedPlane.validGrid`: both decorations remain valid on any regrouped quadrant.
* `ShadedSite.horizontal_iff`, `ShadedSite.vertical_iff`: exact matching semantics.

## References

The obstruction signals are a step of the seed-removal construction in [JeandelVanier2020],
Section 3.3, pp. 26–29 of the authors' manuscript, using its corrected 104-tile alphabet.
The directed encoding and the precise absorption rule here are those of lean-wang's `Signals`.
Prior formalization, revision `64268a3`:
[lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3/LeanWang/Robinson/Closed104),
modules `QuarterRegrouping` (`phase_even`, `exists_southwest_origin`, `block_spec`),
`Signals`, `ShadedSignals`, `ShadedSignalRoutingScaffold` and
`ShadedRoutedPlaneDecode`.
-/

public section
namespace Cslib.WangTile.Robinson

/-- Quarter edge codes retain the corrected parent index and quadrant. -/
theorem quarterTile_injective : Function.Injective quarterTile := by
  rintro ⟨i, q⟩ ⟨j, r⟩ h
  cases q <;> cases r <;>
    simp_all [quarterTile, subdivideTileAt,
      horizontalEdgeColor, verticalEdgeColor,
      internalHorizontalColor, internalVerticalColor,
      Nat.pair_eq_pair, tile_components_injective.eq_iff]

/-- A matching plane of quarter sites, before regrouping into corrected parent tiles. -/
structure QuarterPlane where
  /-- Quarter site at each integer position. -/
  quarter : ℤ → ℤ → QuarterIndex
  /-- Horizontal matching in the subdivided alphabet. -/
  horizontal : ∀ x y,
    (quarterTile (quarter x y)).right = (quarterTile (quarter (x + 1) y)).left
  /-- Vertical matching in the subdivided alphabet. -/
  vertical : ∀ x y,
    (quarterTile (quarter x y)).top = (quarterTile (quarter x (y + 1))).bottom

namespace QuarterPlane

private def eastPhase : Quadrant → Quadrant
  | .southwest => .southeast
  | .southeast => .southwest
  | .northwest => .northeast
  | .northeast => .northwest

private def northPhase : Quadrant → Quadrant
  | .southwest => .northwest
  | .southeast => .northeast
  | .northwest => .southwest
  | .northeast => .southeast

private theorem phase_east (P : QuarterPlane) (x y : ℤ) :
    (P.quarter (x + 1) y).quadrant = eastPhase (P.quarter x y).quadrant := by
  have h := (subdivideTileAt_horizontal_iff _ _
    (P.quarter x y).quadrant (P.quarter (x + 1) y).quadrant).mp (P.horizontal x y)
  cases hl : (P.quarter x y).quadrant <;> cases hr : (P.quarter (x + 1) y).quadrant <;>
    simp_all [eastPhase]

private theorem phase_north (P : QuarterPlane) (x y : ℤ) :
    (P.quarter x (y + 1)).quadrant = northPhase (P.quarter x y).quadrant := by
  have h := (subdivideTileAt_vertical_iff _ _
    (P.quarter x y).quadrant (P.quarter x (y + 1)).quadrant).mp (P.vertical x y)
  cases hl : (P.quarter x y).quadrant <;> cases hr : (P.quarter x (y + 1)).quadrant <;>
    simp_all [northPhase]

private theorem exists_origin (P : QuarterPlane) :
    ∃ x y : ℤ, (P.quarter x y).quadrant = .southwest := by
  have he := phase_east P 0 0
  cases h : (P.quarter 0 0).quadrant with
  | southwest => exact ⟨0, 0, h⟩
  | southeast => exact ⟨1, 0, by simpa [h, eastPhase] using he⟩
  | northwest => exact ⟨0, 1, by simpa [h, northPhase] using phase_north P 0 0⟩
  | northeast =>
    have h₁ : (P.quarter 1 0).quadrant = .northwest := by simpa [h, eastPhase] using he
    exact ⟨1, 1, by simpa [h₁, northPhase] using phase_north P 1 0⟩

private theorem internal_horizontal {a b : QuarterIndex}
    (hphase : a.quadrant.xBit = false)
    (hmatch : (quarterTile a).right = (quarterTile b).left) : a.index = b.index := by
  have h := (subdivideTileAt_horizontal_iff _ _ a.quadrant b.quadrant).mp hmatch
  cases ha : a.quadrant <;> cases hb : b.quadrant <;>
    simp_all [Quadrant.xBit, tile_components_injective.eq_iff]

private theorem internal_vertical {a b : QuarterIndex}
    (hphase : a.quadrant.yBit = false)
    (hmatch : (quarterTile a).top = (quarterTile b).bottom) : a.index = b.index := by
  have h := (subdivideTileAt_vertical_iff _ _ a.quadrant b.quadrant).mp hmatch
  cases ha : a.quadrant <;> cases hb : b.quadrant <;>
    simp_all [Quadrant.yBit, tile_components_injective.eq_iff]

private theorem block_spec (P : QuarterPlane) {x y : ℤ}
    (hphase : (P.quarter x y).quadrant = .southwest) :
    P.quarter x y = ⟨(P.quarter x y).index, .southwest⟩ ∧
    P.quarter (x + 1) y = ⟨(P.quarter x y).index, .southeast⟩ ∧
    P.quarter x (y + 1) = ⟨(P.quarter x y).index, .northwest⟩ ∧
    P.quarter (x + 1) (y + 1) = ⟨(P.quarter x y).index, .northeast⟩ := by
  have he : (P.quarter (x + 1) y).quadrant = .southeast := by simp [phase_east, hphase, eastPhase]
  have hn : (P.quarter x (y + 1)).quadrant = .northwest := by simp [phase_north, hphase, northPhase]
  have hen : (P.quarter (x + 1) (y + 1)).quadrant = .northeast := by
    simp [phase_east, hn, eastPhase]
  have hie := internal_horizontal (by simp [hphase, Quadrant.xBit]) (P.horizontal x y)
  have hin := internal_vertical (by simp [hphase, Quadrant.yBit]) (P.vertical x y)
  have hien := internal_horizontal (by simp [hn, Quadrant.xBit]) (P.horizontal x (y + 1))
  have eq {q : QuarterIndex} {i r} (hi : q.index = i) (hr : q.quadrant = r) : q = ⟨i, r⟩ := by
    cases q
    simp_all
  exact ⟨eq rfl hphase, eq hie.symm he, eq hin.symm hn, eq (hien.symm.trans hin.symm) hen⟩

/-- An exact regrouping of a quarter plane into matching corrected parent tiles. -/
structure Regrouped (Q : QuarterPlane) where
  /-- Southwest corner of the parent at the origin. -/
  origin : ℤ × ℤ
  /-- The matching corrected parent plane. -/
  parent : IndexPlane
  /-- All four quarters in every parent block have that parent index and the expected phase. -/
  blocks : ∀ x y,
    Q.quarter (origin.1 + 2 * x) (origin.2 + 2 * y) =
      ⟨parent.index x y, .southwest⟩ ∧
    Q.quarter (origin.1 + 2 * x + 1) (origin.2 + 2 * y) =
      ⟨parent.index x y, .southeast⟩ ∧
    Q.quarter (origin.1 + 2 * x) (origin.2 + 2 * y + 1) =
      ⟨parent.index x y, .northwest⟩ ∧
    Q.quarter (origin.1 + 2 * x + 1) (origin.2 + 2 * y + 1) =
      ⟨parent.index x y, .northeast⟩

/-- Matching subdivision phases fix a global alignment; internal seams recover each parent. -/
noncomputable def regroup (Q : QuarterPlane) : Regrouped Q := by
  classical
  let ox := Classical.choose (exists_origin Q)
  let oy := Classical.choose (Classical.choose_spec (exists_origin Q))
  have origin : (Q.quarter ox oy).quadrant = .southwest :=
    Classical.choose_spec (Classical.choose_spec (exists_origin Q))
  let index x y := (Q.quarter (ox + 2 * x) (oy + 2 * y)).index
  have blocks x y := block_spec Q ((phase_even_of_involutive
    (fun x y => (Q.quarter x y).quadrant) eastPhase northPhase
    (by intro q; cases q <;> rfl) (by intro q; cases q <;> rfl)
    (phase_east Q) (phase_north Q) ox oy x y).trans origin)
  let parent : IndexPlane := {
    index := index
    horizontal := by
      intro x y
      have h := Q.horizontal (ox + 2 * x + 1) (oy + 2 * y)
      have he : ox + 2 * x + 1 + 1 = ox + 2 * (x + 1) := by omega
      rw [(blocks x y).2.1, he, (blocks (x + 1) y).1] at h
      exact (subdivideTileAt_horizontal_iff _ _ .southeast .southwest).mp h
    vertical := by
      intro x y
      have h := Q.vertical (ox + 2 * x) (oy + 2 * y + 1)
      have hn : oy + 2 * y + 1 + 1 = oy + 2 * (y + 1) := by omega
      rw [(blocks x y).2.2.1, hn, (blocks x (y + 1)).1] at h
      exact (subdivideTileAt_vertical_iff _ _ .northwest .southwest).mp h }
  exact ⟨(ox, oy), parent, blocks⟩

end QuarterPlane

-- Expose the equality computation used by downstream finite signal certificates.
@[expose] public section
/-- Direction relative to the positive coordinate direction of an edge. -/
inductive SignalFlow where
  | none | forward | backward
  deriving DecidableEq
end

namespace SignalFlow

/-- Numerical signal edge code: no signal, positive signal, negative signal. -/
private def code : SignalFlow → ℕ
  | .none => 0
  | .forward => 1
  | .backward => 2

@[simp] private theorem code_eq_zero {f : SignalFlow} : f.code = 0 ↔ f = .none := by
  cases f <;> simp [code]

/-- Distinct signal directions have distinct edge colours. -/
private theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp_all [code]

private def all : List SignalFlow := [.none, .forward, .backward]

private theorem mem_all (f : SignalFlow) : f ∈ all := by cases f <;> decide

end SignalFlow

-- Expose the derived equality so clients can decide the clear-state role characterizations.
@[expose] public section
/-- Directed obstruction signals on the four edges of a quarter tile. -/
structure SignalState where
  /-- West-edge flow. -/
  west : SignalFlow
  /-- East-edge flow. -/
  east : SignalFlow
  /-- South-edge flow. -/
  south : SignalFlow
  /-- North-edge flow. -/
  north : SignalFlow
  deriving DecidableEq
end

/-- The state with all four signal directions absent. -/
@[expose] def SignalState.clear : SignalState := ⟨.none, .none, .none, .none⟩

private def SignalState.all : List SignalState :=
  SignalFlow.all.flatMap fun west => SignalFlow.all.flatMap fun east =>
    SignalFlow.all.flatMap fun south => SignalFlow.all.map fun north => ⟨west, east, south, north⟩

private theorem SignalState.mem_all (s : SignalState) : s ∈ SignalState.all := by
  cases s
  simp [SignalState.all, SignalFlow.mem_all]

/-- The one-dimensional obstruction rule. A positive interior is east or north. -/
@[expose] def flowAllowed (interior : Option Bool) (before after : SignalFlow) : Bool :=
  match interior with
  | none => decide (before = after)
  | some true => decide (before ≠ .none ∧ after ≠ .forward)
  | some false => decide (after ≠ .none ∧ before ≠ .backward)

/-- Code west as negative and east as positive; absence remains absent. -/
@[expose] def horizontalInteriorCode : Option HorizontalDirection → Option Bool
  | none => none
  | some .west => some false
  | some .east => some true

/-- Code south as negative and north as positive; absence remains absent. -/
@[expose] def verticalInteriorCode : Option VerticalDirection → Option Bool
  | none => none
  | some .south => some false
  | some .north => some true

/-- Apply the common obstruction rule to the two horizontal edges. -/
@[expose] def SignalState.horizontalAllowed (interior : Option HorizontalDirection)
    (s : SignalState) : Bool :=
  flowAllowed (horizontalInteriorCode interior) s.west s.east

/-- Apply the common obstruction rule to the two vertical edges. -/
@[expose] def SignalState.verticalAllowed (interior : Option VerticalDirection)
    (s : SignalState) : Bool :=
  flowAllowed (verticalInteriorCode interior) s.south s.north

/-- The horizontal and vertical obstruction rules for the selected light borders. -/
@[expose] def signalsAllowed (quarter : QuarterIndex) (shade : ShadeState)
    (signal : SignalState) : Bool :=
  SignalState.horizontalAllowed
      (selectedVerticalFor (components quarter.index).thick quarter.quadrant shade) signal &&
    SignalState.verticalAllowed
      (selectedHorizontalFor (components quarter.index).thick quarter.quadrant shade) signal

/-- A decorated site has independent quarter, red-shade and obstruction-signal components.
Admissibility is checked when forming the finite palette. -/
structure ShadedSite where
  /-- The corrected tile and its quadrant. -/
  quarter : QuarterIndex
  /-- The light/dark decoration of its red paths. -/
  shade : ShadeState
  /-- Its directed obstruction signals. -/
  signal : SignalState

/-- Code optional red shades as edge colours: absent is zero, light is one, dark is two.
The canonical seam certificates use the same coding as the scaffold's shade layer. -/
@[expose] def Shade.code : Option Shade → ℕ
  | none => 0
  | some .light => 1
  | some .dark => 2

/-- The shade edge code retains absence and both shades. -/
theorem Shade.code_injective : Function.Injective Shade.code := by
  intro a b h
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · cases b <;> simp [Shade.code] at h
  · cases a <;> simp [Shade.code] at h
  · cases a <;> cases b <;> simp_all [Shade.code]

namespace ShadedSite

private def shadeTile (s : ShadeState) : WangTile :=
  ⟨Shade.code s.north, Shade.code s.south, Shade.code s.west, Shade.code s.east⟩

private def signalTile (s : SignalState) : WangTile :=
  ⟨s.north.code, s.south.code, s.west.code, s.east.code⟩

/-- Each edge pairs the quarter colour with the shade code, then with the signal code. -/
def tile (s : ShadedSite) : WangTile :=
  layer (layer (quarterTile s.quarter) (shadeTile s.shade)) (signalTile s.signal)

private def allSites : List ShadedSite :=
  (List.finRange 104).flatMap fun index =>
    Quadrant.all.flatMap fun quadrant =>
      (ShadeState.all.filter fun shade =>
        Robinson.locallyAllowed ⟨index, quadrant⟩ shade).flatMap fun shade =>
          (SignalState.all.filter fun signal =>
            signalsAllowed ⟨index, quadrant⟩ shade signal).map fun signal =>
              ⟨⟨index, quadrant⟩, shade, signal⟩

private theorem mem_allSites (s : ShadedSite) :
    s ∈ allSites ↔ Robinson.locallyAllowed s.quarter s.shade = true ∧
      signalsAllowed s.quarter s.shade s.signal = true := by
  rcases s with ⟨⟨index, quadrant⟩, shade, signal⟩
  simp [allSites, Quadrant.mem_all, SignalState.mem_all]

/-- Horizontal matching means quarter matching and equality of both decorations. -/
theorem horizontal_iff (a b : ShadedSite) :
    (tile a).right = (tile b).left ↔
      (quarterTile a.quarter).right = (quarterTile b.quarter).left ∧
      a.shade.east = b.shade.west ∧ a.signal.east = b.signal.west := by
  simp [tile, layer, shadeTile, signalTile, Nat.pair_eq_pair,
    Shade.code_injective.eq_iff, SignalFlow.code_injective.eq_iff, and_assoc]

/-- Vertical matching means quarter matching and equality of both decorations. -/
theorem vertical_iff (a b : ShadedSite) :
    (tile a).top = (tile b).bottom ↔
      (quarterTile a.quarter).top = (quarterTile b.quarter).bottom ∧
      a.shade.north = b.shade.south ∧ a.signal.north = b.signal.south := by
  simp [tile, layer, shadeTile, signalTile, Nat.pair_eq_pair,
    Shade.code_injective.eq_iff, SignalFlow.code_injective.eq_iff, and_assoc]

private def horizontalClear (t : WangTile) : Bool :=
  decide ((Nat.unpair t.left).2 = 0 ∧ (Nat.unpair t.right).2 = 0)

private def verticalClear (t : WangTile) : Bool :=
  decide ((Nat.unpair t.bottom).2 = 0 ∧ (Nat.unpair t.top).2 = 0)

private def quarterLayer (t : WangTile) : WangTile :=
  ⟨(Nat.unpair (Nat.unpair t.top).1).1, (Nat.unpair (Nat.unpair t.bottom).1).1,
    (Nat.unpair (Nat.unpair t.left).1).1, (Nat.unpair (Nat.unpair t.right).1).1⟩

/-- The effective role decoder. Clear crossings at index zero's northeast quarter carry the seed. -/
def routeRole (t : WangTile) : RouteRole :=
  if horizontalClear t then
    if verticalClear t then
      if quarterLayer t = quarterTile ⟨0, .northeast⟩ then .corner else .active
    else .horizontal
  else if verticalClear t then .vertical else .inactive

/-- The local role is computed from the two clear directions and the unique marker quarter. -/
theorem routeRole_tile (s : ShadedSite) :
    routeRole (tile s) =
      if s.signal.west = .none ∧ s.signal.east = .none then
        if s.signal.south = .none ∧ s.signal.north = .none then
          if s.quarter = ⟨0, .northeast⟩ then .corner else .active
        else .horizontal
      else if s.signal.south = .none ∧ s.signal.north = .none then .vertical else .inactive := by
  simp [routeRole, horizontalClear, verticalClear, quarterLayer, tile, layer,
    signalTile, quarterTile_injective.eq_iff]

/-- A site carries horizontal data exactly when both horizontal signal edges are clear. -/
theorem horizontalCarrier_iff (s : ShadedSite) :
    (routeRole (tile s)).horizontalCarrier = true ↔
      s.signal.west = .none ∧ s.signal.east = .none := by
  rw [routeRole_tile]
  split_ifs <;> simp_all [RouteRole.horizontalCarrier]

/-- A site carries vertical data exactly when both vertical signal edges are clear. -/
theorem verticalCarrier_iff (s : ShadedSite) :
    (routeRole (tile s)).verticalCarrier = true ↔
      s.signal.south = .none ∧ s.signal.north = .none := by
  rw [routeRole_tile]
  split_ifs <;> simp_all [RouteRole.verticalCarrier]

/-- The unique seeded role is an all-clear northeast quarter of corrected index zero. -/
theorem corner_iff (s : ShadedSite) :
    routeRole (tile s) = .corner ↔
      s.signal = SignalState.clear ∧ s.quarter = ⟨0, .northeast⟩ := by
  rcases s with ⟨q, sh, ⟨w, e, so, no⟩⟩
  rw [routeRole_tile]
  simp only [SignalState.clear, SignalState.mk.injEq]
  split_ifs <;> simp_all

/-- Horizontal wire cells have clear horizontal signals and a blocked vertical direction. -/
theorem horizontal_iff_role (s : ShadedSite) :
    routeRole (tile s) = .horizontal ↔
      (s.signal.west = .none ∧ s.signal.east = .none) ∧
        ¬ (s.signal.south = .none ∧ s.signal.north = .none) := by
  rw [routeRole_tile]
  split_ifs <;> simp_all

/-- Vertical wire cells have a blocked horizontal direction and clear vertical signals. -/
theorem vertical_iff_role (s : ShadedSite) :
    routeRole (tile s) = .vertical ↔
      ¬ (s.signal.west = .none ∧ s.signal.east = .none) ∧
        s.signal.south = .none ∧ s.signal.north = .none := by
  rw [routeRole_tile]
  split_ifs <;> simp_all

/-- Simultaneous clear directions give a crossing, possibly the seeded crossing. -/
theorem crossing_iff (s : ShadedSite) :
    (routeRole (tile s) = .active ∨ routeRole (tile s) = .corner) ↔
      s.signal = SignalState.clear := by
  rcases s with ⟨q, sh, ⟨w, e, so, no⟩⟩
  rw [routeRole_tile]
  simp only [SignalState.clear, SignalState.mk.injEq]
  split_ifs <;> simp_all

end ShadedSite

/-- The corrected shaded Robinson obstruction scaffold with its payload roles. -/
def scaffold : RoutedScaffold where
  tiles := ShadedSite.allSites.map ShadedSite.tile
  role := ShadedSite.routeRole

/-- The scaffold uses the concrete clear-edge role decoder. -/
@[simp] theorem scaffold_role : scaffold.role = ShadedSite.routeRole := by rfl

namespace ShadedSite

/-- Scaffold membership is exactly local shade and signal admissibility. -/
theorem mem_scaffold {t : WangTile} :
    t ∈ scaffold.tiles ↔ ∃ s : ShadedSite,
      Robinson.locallyAllowed s.quarter s.shade = true ∧
      signalsAllowed s.quarter s.shade s.signal = true ∧ tile s = t := by
  simp [scaffold, mem_allSites, and_assoc]

/-- A locally admissible decorated site belongs to the concrete scaffold. -/
theorem tile_mem (s : ShadedSite)
    (hshade : Robinson.locallyAllowed s.quarter s.shade = true)
    (hsignal : signalsAllowed s.quarter s.shade s.signal = true) :
    tile s ∈ scaffold.tiles :=
  mem_scaffold.mpr ⟨s, hshade, hsignal, rfl⟩

end ShadedSite

/-- The semantic content of a scaffold plane; all components retain their shared-edge rules. -/
structure DecodedPlane (P : Plane scaffold.tiles) where
  /-- The three components at each position. -/
  site : ℤ → ℤ → ShadedSite
  /-- The components encode the original tile. -/
  tile_eq : ∀ x y, ShadedSite.tile (site x y) = P.tile x y
  /-- Local shade rules. -/
  shadeAllowed : ∀ x y,
    Robinson.locallyAllowed (site x y).quarter (site x y).shade = true
  /-- Local obstruction rules. -/
  signalAllowed : ∀ x y,
    signalsAllowed (site x y).quarter (site x y).shade (site x y).signal = true
  /-- Quarter and both decoration edges match horizontally. -/
  horizontal : ∀ x y,
    (quarterTile (site x y).quarter).right =
        (quarterTile (site (x + 1) y).quarter).left ∧
      (site x y).shade.east = (site (x + 1) y).shade.west ∧
      (site x y).signal.east = (site (x + 1) y).signal.west
  /-- Quarter and both decoration edges match vertically. -/
  vertical : ∀ x y,
    (quarterTile (site x y).quarter).top =
        (quarterTile (site x (y + 1)).quarter).bottom ∧
      (site x y).shade.north = (site x (y + 1)).shade.south ∧
      (site x y).signal.north = (site x (y + 1)).signal.south

/-- Decode any ordinary scaffold plane; no choice of special plane or hierarchy is assumed. -/
noncomputable def DecodedPlane.ofPlane (P : Plane scaffold.tiles) :
    DecodedPlane P := by
  classical
  choose s hs ht he using fun x y => ShadedSite.mem_scaffold.mp (P.mem x y)
  refine ⟨s, he, hs, ht, ?_, ?_⟩
  · intro x y
    apply (ShadedSite.horizontal_iff _ _).mp
    rw [he, he]
    exact P.horizontal x y
  · intro x y
    apply (ShadedSite.vertical_iff _ _).mp
    rw [he, he]
    exact P.vertical x y

namespace DecodedPlane

/-- Forget decorations while retaining matching of quarter edges. -/
@[expose] def quarterPlane {P : Plane scaffold.tiles} (D : DecodedPlane P) :
    QuarterPlane where
  quarter x y := (D.site x y).quarter
  horizontal x y := (D.horizontal x y).1
  vertical x y := (D.vertical x y).1

end DecodedPlane

namespace QuarterPlane.Regrouped

/-- Regrouping describes every natural quarter coordinate above any parent origin. -/
theorem quarter_at {Q : QuarterPlane} (R : QuarterPlane.Regrouped Q)
    (a b : ℤ) (x y : ℕ) :
    Q.quarter (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y) =
      ⟨R.parent.index (a + (x / 2 : ℕ)) (b + (y / 2 : ℕ)),
        quadrantAt x y⟩ := by
  have hx : R.origin.1 + 2 * a + x = R.origin.1 + 2 * (a + (x / 2 : ℕ)) + (x % 2 : ℕ) := by omega
  have hy : R.origin.2 + 2 * b + y = R.origin.2 + 2 * (b + (y / 2 : ℕ)) + (y % 2 : ℕ) := by omega
  have blocks := R.blocks (a + (x / 2 : ℕ)) (b + (y / 2 : ℕ))
  rw [hx, hy]
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy
  · simpa [hx, hy, quadrantAt, Quadrant.ofBits] using blocks.1
  · simpa [hx, hy, quadrantAt, Quadrant.ofBits] using blocks.2.2.1
  · simpa [hx, hy, quadrantAt, Quadrant.ofBits] using blocks.2.1
  · simpa [hx, hy, quadrantAt, Quadrant.ofBits] using blocks.2.2.2

end QuarterPlane.Regrouped

/-- Compatible shade and signal assignments on the natural quarter grid of an indexed plane. -/
structure ValidSignalGrid (indexGrid : ℕ → ℕ → Index)
    (shadeGrid : ℕ → ℕ → ShadeState) (signalGrid : ℕ → ℕ → SignalState) : Prop where
  /-- Local incidence, propagation and matching of the shades. -/
  shadeValid : ValidShadeGrid indexGrid shadeGrid
  /-- Both signal directions obey the selected light-border rules. -/
  signalAllowed : ∀ x y,
    signalsAllowed ⟨indexGrid (x / 2) (y / 2), quadrantAt x y⟩
      (shadeGrid x y) (signalGrid x y) = true
  /-- Horizontal signal edges match. -/
  horizontal : ∀ x y, (signalGrid x y).east = (signalGrid (x + 1) y).west
  /-- Vertical signal edges match. -/
  vertical : ∀ x y, (signalGrid x y).north = (signalGrid x (y + 1)).south

namespace DecodedPlane

/-- Restrict a decoded plane to natural quarter coordinates above a chosen parent origin. -/
@[expose] def siteGrid {P : Plane scaffold.tiles} (D : DecodedPlane P)
    (R : QuarterPlane.Regrouped D.quarterPlane) (a b : ℤ) (x y : ℕ) : ShadedSite :=
  D.site (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)

/-- Both decorations of an arbitrary decoded plane remain valid on its regrouped quarter grid. -/
theorem validGrid {P : Plane scaffold.tiles} (D : DecodedPlane P)
    (R : QuarterPlane.Regrouped D.quarterPlane) (a b : ℤ) :
    ValidSignalGrid (fun i j => R.parent.index (a + i) (b + j))
      (fun x y => (D.siteGrid R a b x y).shade)
      (fun x y => (D.siteGrid R a b x y).signal) := by
  refine ⟨⟨fun x y => ?_, fun x y => ?_, fun x y => ?_⟩,
    fun x y => ?_, fun x y => ?_, fun x y => ?_⟩
  · simpa only [siteGrid, quarterPlane, ← R.quarter_at] using
      D.shadeAllowed (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)
  · simpa [siteGrid, add_assoc] using
      (D.horizontal (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)).2.1
  · simpa [siteGrid, add_assoc] using
      (D.vertical (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)).2.1
  · simpa only [siteGrid, quarterPlane, ← R.quarter_at] using
      D.signalAllowed (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)
  · simpa [siteGrid, add_assoc] using
      (D.horizontal (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)).2.2
  · simpa [siteGrid, add_assoc] using
      (D.vertical (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)).2.2

end DecodedPlane

end Cslib.WangTile.Robinson
