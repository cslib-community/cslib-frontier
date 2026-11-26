/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Pointed
import CslibFrontier.Computability.WangTile.Compactness

/-!
# Routed scaffolds and generic seed removal

A finite scaffold assigns a routing role to each tile. Pairing its edge colours with payload
colours lets crossings carry payload tiles and wires transmit one colour. Inactive edges use
zero or a colour occurring in the payload palette.

## Main definitions

* `RouteRole`, `RoutedScaffold`, `combine`: the finite routed construction.
* `Plane`, `RoutedPlane`, `RoutedGrid`: matching planes and finite grids of crossings and wires.
* `AddressedSquare`: a matching scaffold patch with compatible integer payload addresses.
* `Forces`, `Realizes`: the two geometric obligations for seed removal.

## Main results

* `primrec_combine`: the finite combination is primitive recursive.
* `forces_of_routedGrids`: routed grids extract seeded payload squares.
* `realizes_of_addressedSquares`: cofinal addressed squares realize pointed payload planes.
* `tilesPlane_combine_pointedExtension_iff_of_forces_of_realizes`: the generic seed-removal
  step, conditional on both obligations. This is not the domino undecidability theorem.

## References

Restructured from [lean-wang, revision 64268a3, routed scaffolds](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Scaffold/Routed.lean)
and its `PointedCarrierAddressing` and `PointedPlane` modules. The construction is a step of
the seed-removal argument in [JeandelVanier2020], §3.3, pp. 26–29, after [Robinson1971].
The roles separate crossings from intervening wire cells, and the two obligations isolate the
arbitrarily large seeded-square and pointed-plane construction steps; no concrete scaffold
obligations are assumed proved here. For the corrected Robinson scaffold, the later Forcing
and Realization modules must establish these obligations.
-/

public section

namespace Cslib.WangTile

/-- A tile's payload role: unconstrained, a wire, a crossing, or a seeded crossing. -/
inductive RouteRole where
  | inactive | horizontal | vertical | active | corner
  deriving DecidableEq

/-- Whether the role prescribes horizontal payload data. -/
@[expose] def RouteRole.horizontalCarrier : RouteRole → Bool
  | .horizontal | .active | .corner => true
  | _ => false

/-- Whether the role prescribes vertical payload data. -/
@[expose] def RouteRole.verticalCarrier : RouteRole → Bool
  | .vertical | .active | .corner => true
  | _ => false

/-- A finite scaffold with an assigned payload role at each tile. -/
structure RoutedScaffold where
  /-- The finite scaffold alphabet. -/
  tiles : List WangTile
  /-- The payload role attached to a scaffold tile. -/
  role : WangTile → RouteRole

/-- Pair scaffold and payload colours on each edge, in that order. -/
@[expose] def layer (base payload : WangTile) : WangTile :=
  ⟨Nat.pair base.top payload.top, Nat.pair base.bottom payload.bottom,
    Nat.pair base.left payload.left, Nat.pair base.right payload.right⟩

private def palette (τ : List WangTile) : List ℕ :=
  0 :: τ.flatMap fun t => [t.top, t.bottom, t.left, t.right]

/-- All tiles whose four colours are zero or occur on some payload tile. -/
def completePayloads (τ : List WangTile) : List WangTile :=
  let c := palette τ
  c.flatMap fun top => c.flatMap fun bottom => c.flatMap fun left =>
    c.map fun right => ⟨top, bottom, left, right⟩

/-- Payloads allowed at a scaffold tile. Corners require the seed to belong to the palette. -/
def routedPayloads (S : RoutedScaffold) (I : SeededInstance) (base : WangTile) :
    List WangTile :=
  match S.role base with
  | .inactive => completePayloads I.tiles
  | .horizontal => (completePayloads I.tiles).filter fun p => p.left = p.right
  | .vertical => (completePayloads I.tiles).filter fun p => p.bottom = p.top
  | .active => I.tiles
  | .corner => I.tiles.filter fun p => p = I.seed

/-- Finite routed combination, with scaffold colour first in each `Nat.pair` edge code. -/
def combine (S : RoutedScaffold) (I : SeededInstance) : List WangTile :=
  S.tiles.flatMap fun base => (routedPayloads S I base).map (layer base)

/-- Membership exposes the two finite layers and the local payload constraint. -/
theorem mem_combine {S : RoutedScaffold} {I : SeededInstance} {t : WangTile} :
    t ∈ combine S I ↔ ∃ b ∈ S.tiles, ∃ p ∈ routedPayloads S I b, layer b p = t := by
  simp [combine]

private theorem mem_completePayloads {τ : List WangTile} {p : WangTile} :
    p ∈ completePayloads τ ↔ p.top ∈ palette τ ∧ p.bottom ∈ palette τ ∧
      p.left ∈ palette τ ∧ p.right ∈ palette τ := by
  cases p
  simp [completePayloads]

/-- Every input tile belongs to the palette completed under independent edge choices. -/
theorem mem_completePayloads_of_mem {τ : List WangTile} {p : WangTile}
    (hp : p ∈ τ) : p ∈ completePayloads τ := by
  rw [mem_completePayloads]
  have edges (c : ℕ) (hc : c ∈ [p.top, p.bottom, p.left, p.right]) : c ∈ palette τ :=
    List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩)
  exact ⟨edges _ (by simp), edges _ (by simp), edges _ (by simp), edges _ (by simp)⟩

/-- The local role constraint, with explicit finite colour bounds on inactive edges. -/
theorem mem_routedPayloads {S : RoutedScaffold} {I : SeededInstance} {b p : WangTile} :
    p ∈ routedPayloads S I b ↔
      match S.role b with
      | .inactive => p ∈ completePayloads I.tiles
      | .horizontal => p ∈ completePayloads I.tiles ∧ p.left = p.right
      | .vertical => p ∈ completePayloads I.tiles ∧ p.bottom = p.top
      | .active => p ∈ I.tiles
      | .corner => p ∈ I.tiles ∧ p = I.seed := by
  cases h : S.role b <;> simp [routedPayloads, h]

private theorem primrec_completePayloads : Primrec completePayloads := by
  have hc : Primrec palette :=
    Primrec.list_cons.comp (.const 0) (.list_flatMap .id (.mk ((Primrec.list_cons.comp primrec_top
      (Primrec.list_cons.comp primrec_bottom (Primrec.list_cons.comp primrec_left
        (Primrec.list_cons.comp primrec_right (.const []))))).comp .snd)))
  exact Primrec.list_flatMap hc (.mk <| .list_flatMap (hc.comp .fst) (.mk <|
    .list_flatMap (hc.comp (.comp .fst .fst)) (.mk <|
      .list_map (hc.comp (.comp .fst (.comp .fst .fst))) (.mk <|
        primrec_mk (.comp .snd (.comp .fst (.comp .fst .fst)))
          (.comp .snd (.comp .fst .fst)) (.comp .snd .fst) .snd))))

/-- The combination is primitive recursive on the seeded instance code: only the finitely many
roles on the fixed scaffold alphabet matter, so no computability premise on `S.role` is needed. -/
theorem primrec_combine (S : RoutedScaffold) : Primrec (combine S) := by
  have hp (b : WangTile) : Primrec (fun I => routedPayloads S I b) := by
    have hcp := primrec_completePayloads.comp SeededInstance.primrec_tiles
    cases h : S.role b
    · exact hcp.of_eq fun _ => by simp [routedPayloads, h]
    · exact ((Primrec.listFilter (Primrec.eq.comp primrec_left primrec_right)).comp hcp).of_eq
        fun _ => by simp [routedPayloads, h]
    · exact ((Primrec.listFilter (Primrec.eq.comp primrec_bottom primrec_top)).comp hcp).of_eq
        fun _ => by simp [routedPayloads, h]
    · exact SeededInstance.primrec_tiles.of_eq fun _ => by simp [routedPayloads, h]
    · exact ((PrimrecRel.listFilter Primrec.eq).comp SeededInstance.primrec_tiles
        SeededInstance.primrec_seed).of_eq fun _ => by simp [routedPayloads, h]
  have hl (b : WangTile) : Primrec (layer b) :=
    primrec_mk (Primrec₂.natPair.comp (.const b.top) primrec_top)
      (Primrec₂.natPair.comp (.const b.bottom) primrec_bottom)
      (Primrec₂.natPair.comp (.const b.left) primrec_left)
      (Primrec₂.natPair.comp (.const b.right) primrec_right)
  unfold combine
  induction S.tiles with
  | nil => exact .const []
  | cons b _ ih => exact Primrec.list_append.comp (.list_map (hp b) (.mk ((hl b).comp .snd))) ih

/-- A matching plane, bundled for geometric constructions. This uses exactly `TilesPlane`. -/
structure Plane (τ : List WangTile) where
  /-- The tile at integer coordinates. -/
  tile : ℤ → ℤ → WangTile
  /-- Every tile belongs to the palette. -/
  mem : ∀ x y, tile x y ∈ τ
  /-- Horizontal matching. -/
  horizontal : ∀ x y, (tile x y).right = (tile (x + 1) y).left
  /-- Vertical matching. -/
  vertical : ∀ x y, (tile x y).top = (tile x (y + 1)).bottom

/-- The bundled and existential plane predicates describe the same tilings. -/
theorem nonempty_plane_iff (τ : List WangTile) : Nonempty (Plane τ) ↔ TilesPlane τ :=
  ⟨fun ⟨p⟩ => ⟨p.tile, fun x y => ⟨p.mem x y, p.horizontal x y, p.vertical x y⟩⟩,
   fun ⟨f, hf⟩ => ⟨⟨f, fun x y => (hf x y).1, fun x y => (hf x y).2.1, fun x y => (hf x y).2.2⟩⟩⟩

/-- A matching routed plane separated into its scaffold and payload layers. -/
structure RoutedPlane (S : RoutedScaffold) (I : SeededInstance) where
  /-- The underlying scaffold plane. -/
  base : Plane S.tiles
  /-- The payload at each integer position. -/
  payload : ℤ → ℤ → WangTile
  /-- Payloads obey the local role. -/
  allowed : ∀ x y, payload x y ∈ routedPayloads S I (base.tile x y)
  /-- Horizontal payload matching. -/
  horizontal : ∀ x y, (payload x y).right = (payload (x + 1) y).left
  /-- Vertical payload matching. -/
  vertical : ∀ x y, (payload x y).top = (payload x (y + 1)).bottom

/-- Decode the two layers of a combined tiling; edge pairing preserves both matchings. -/
theorem nonempty_routedPlane_of_tilesPlane {S : RoutedScaffold} {I : SeededInstance}
    (h : TilesPlane (combine S I)) : Nonempty (RoutedPlane S I) := by
  classical
  obtain ⟨f, hf⟩ := h
  choose b hb p hp he using fun x y => mem_combine.mp (hf x y).1
  have hh x y := Nat.pair_eq_pair.mp (by simpa only [← he, layer] using (hf x y).2.1 :
    Nat.pair (b x y).right (p x y).right = Nat.pair (b (x + 1) y).left (p (x + 1) y).left)
  have hv x y := Nat.pair_eq_pair.mp (by simpa only [← he, layer] using (hf x y).2.2 :
    Nat.pair (b x y).top (p x y).top = Nat.pair (b x (y + 1)).bottom (p x (y + 1)).bottom)
  exact ⟨⟨⟨b, hb, fun x y => (hh x y).1, fun x y => (hv x y).1⟩,
    p, hp, fun x y => (hh x y).2, fun x y => (hv x y).2⟩⟩

/-- A finite grid whose crossings are linked by horizontal and vertical payload wires. -/
structure RoutedGrid (S : RoutedScaffold) (P : Plane S.tiles) (n : ℕ) where
  /-- Integer positions of consecutive selected columns. -/
  column : Fin (n + 1) → ℤ
  /-- Integer positions of consecutive selected rows. -/
  row : Fin (n + 1) → ℤ
  /-- Columns are strictly ordered. -/
  column_strictMono : StrictMono column
  /-- Rows are strictly ordered. -/
  row_strictMono : StrictMono row
  /-- Each selected intersection carries a payload tile. -/
  crossing : ∀ i j, S.role (P.tile (column i) (row j)) = .active ∨
    S.role (P.tile (column i) (row j)) = .corner
  /-- The southwest intersection carries the seed. -/
  corner : S.role (P.tile (column 0) (row 0)) = .corner
  /-- Every intervening cell on a selected row is a horizontal wire. -/
  horizontal : ∀ (i : Fin n) (j : Fin (n + 1)) (x : ℤ),
    column i.castSucc < x → x < column i.succ →
      S.role (P.tile x (row j)) = .horizontal
  /-- Every intervening cell on a selected column is a vertical wire. -/
  vertical : ∀ (i : Fin (n + 1)) (j : Fin n) (y : ℤ),
    row j.castSucc < y → y < row j.succ →
      S.role (P.tile (column i) y) = .vertical

/-- The logical address on the outgoing horizontal side of a carrier. -/
@[expose] def RouteRole.horizontalOutgoing (role : RouteRole) (point source : ℤ × ℤ) : ℤ × ℤ :=
  match role with
  | .active | .corner => point
  | .horizontal => source
  | _ => (0, 0)

/-- The logical address on the outgoing vertical side of a carrier. -/
@[expose] def RouteRole.verticalOutgoing (role : RouteRole) (point source : ℤ × ℤ) : ℤ × ℤ :=
  match role with
  | .active | .corner => point
  | .vertical => source
  | _ => (0, 0)

/-- A scaffold square with logical crossing and wire addresses. A wire transmits the outgoing
colour of its source. Entering the next crossing advances that address by one in the relevant
axis. Only pairs of cells carrying that axis impose an equation. -/
structure AddressedSquare (S : RoutedScaffold) (n : ℕ) where
  /-- The matching scaffold square, of side `n + 1`. -/
  base : Rectangle S.tiles (n + 1) (n + 1)
  /-- Logical payload coordinate at a crossing. -/
  point : Fin (n + 1) → Fin (n + 1) → ℤ × ℤ
  /-- Logical source of a horizontal wire's transmitted right colour. -/
  horizontalSource : Fin (n + 1) → Fin (n + 1) → ℤ × ℤ
  /-- Logical source of a vertical wire's transmitted top colour. -/
  verticalSource : Fin (n + 1) → Fin (n + 1) → ℤ × ℤ
  /-- All seeded crossings use the pointed payload's origin. -/
  corner_zero : ∀ i j, S.role (base.tile i j) = .corner → point i j = (0, 0)
  /-- Horizontal neighbors agree on the transmitted address. A crossing's incoming address
  is its point minus `(1, 0)`. -/
  hstep : ∀ i j (hi : i.val + 1 < n + 1),
    (S.role (base.tile i j)).horizontalCarrier = true →
    (S.role (base.tile ⟨i.val + 1, hi⟩ j)).horizontalCarrier = true →
    let outgoing := (S.role (base.tile i j)).horizontalOutgoing
      (point i j) (horizontalSource i j)
    match S.role (base.tile ⟨i.val + 1, hi⟩ j) with
    | .active | .corner => point ⟨i.val + 1, hi⟩ j = (outgoing.1 + 1, outgoing.2)
    | .horizontal => horizontalSource ⟨i.val + 1, hi⟩ j = outgoing
    | _ => False
  /-- Vertical neighbors agree on the transmitted address. A crossing's incoming address
  is its point minus `(0, 1)`. -/
  vstep : ∀ i j (hj : j.val + 1 < n + 1),
    (S.role (base.tile i j)).verticalCarrier = true →
    (S.role (base.tile i ⟨j.val + 1, hj⟩)).verticalCarrier = true →
    let outgoing := (S.role (base.tile i j)).verticalOutgoing
      (point i j) (verticalSource i j)
    match S.role (base.tile i ⟨j.val + 1, hj⟩) with
    | .active | .corner => point i ⟨j.val + 1, hj⟩ = (outgoing.1, outgoing.2 + 1)
    | .vertical => verticalSource i ⟨j.val + 1, hj⟩ = outgoing
    | _ => False

/-- Every combined plane yields seeded payload squares of every positive side length. -/
@[expose] def Forces (S : RoutedScaffold) : Prop :=
  ∀ I, TilesPlane (combine S I) → ∀ n, Nonempty (SeededSquare I n)

/-- Every payload plane with the seed at the origin lifts to a combined plane. -/
@[expose] def Realizes (S : RoutedScaffold) : Prop :=
  ∀ I, TilesAtOrigin I → TilesPlane (combine S I)

private theorem transmit {incoming outgoing : ℤ → ℕ} (a b : ℤ) (hab : a < b)
    (step : ∀ x, outgoing x = incoming (x + 1))
    (wire : ∀ x, a < x → x < b → incoming x = outgoing x) :
    outgoing a = incoming b := by
  have h : ∀ x, a + 1 ≤ x → x ≤ b → outgoing a = incoming x :=
    Int.leInduction (fun _ => step a) fun x _ ih _ => by
      rw [← step x, ← wire x (by omega) (by omega)]
      exact ih (by omega)
  exact h b (by omega) le_rfl

/-- Extract a seeded payload square by propagating colours along each interval of wires. -/
def RoutedGrid.seededSquare {S : RoutedScaffold} {I : SeededInstance} {n : ℕ}
    (P : RoutedPlane S I) (G : RoutedGrid S P.base n) : SeededSquare I n where
  tile i j := P.payload (G.column i) (G.row j)
  mem i j := by
    have h := mem_routedPayloads.mp (P.allowed (G.column i) (G.row j))
    rcases G.crossing i j with hr | hr
    · simpa only [hr] using h
    · exact (show _ ∧ _ from (by simpa only [hr] using h)).1
  horizontal i j hi := by
    let k : Fin n := ⟨i.val, by omega⟩
    apply transmit (incoming := fun x => (P.payload x (G.row j)).left)
      (outgoing := fun x => (P.payload x (G.row j)).right) (G.column k.castSucc) (G.column k.succ)
      (G.column_strictMono Fin.castSucc_lt_succ) (fun x => P.horizontal x (G.row j))
    intro x hleft hright
    have h := mem_routedPayloads.mp (P.allowed x (G.row j))
    rw [G.horizontal k j x hleft hright] at h
    exact h.2
  vertical i j hj := by
    let k : Fin n := ⟨j.val, by omega⟩
    apply transmit (incoming := fun y => (P.payload (G.column i) y).bottom)
      (outgoing := fun y => (P.payload (G.column i) y).top) (G.row k.castSucc) (G.row k.succ)
      (G.row_strictMono Fin.castSucc_lt_succ) (fun y => P.vertical (G.column i) y)
    intro y hbottom htop
    have h := mem_routedPayloads.mp (P.allowed (G.column i) y)
    rw [G.vertical i k y hbottom htop] at h
    exact h.2
  corner := by
    have h := mem_routedPayloads.mp (P.allowed (G.column 0) (G.row 0))
    rw [G.corner] at h
    exact h.2

/-- Arbitrarily large routed grids in every scaffold plane imply forward forcing. -/
theorem forces_of_routedGrids {S : RoutedScaffold}
    (grids : ∀ (P : Plane S.tiles) n, Nonempty (RoutedGrid S P n)) : Forces S := by
  intro I h n
  obtain ⟨P⟩ := nonempty_routedPlane_of_tilesPlane h
  exact (grids P.base n).map (·.seededSquare P)

private def fillIncoming {n : ℕ} (carry : Fin n → Bool) (incoming outgoing : Fin n → ℕ)
    (i : Fin n) : ℕ :=
  if carry i then incoming i else
    if hi : 0 < i.val then
      let p : Fin n := ⟨i.val - 1, by omega⟩
      if carry p then outgoing p else 0
    else 0

private def fillOutgoing {n : ℕ} (carry : Fin n → Bool) (incoming outgoing : Fin n → ℕ)
    (i : Fin n) : ℕ :=
  if carry i then outgoing i else
    if hi : i.val + 1 < n then
      let p : Fin n := ⟨i.val + 1, hi⟩
      if carry p then incoming p else 0
    else 0

private theorem fill_match {n : ℕ} (carry : Fin n → Bool) (incoming outgoing : Fin n → ℕ)
    (h : ∀ i (hi : i.val + 1 < n), carry i = true →
      carry ⟨i.val + 1, hi⟩ = true → outgoing i = incoming ⟨i.val + 1, hi⟩)
    (i : Fin n) (hi : i.val + 1 < n) :
    fillOutgoing carry incoming outgoing i =
      fillIncoming carry incoming outgoing ⟨i.val + 1, hi⟩ := by
  by_cases hc : carry i = true <;>
    by_cases hn : carry ⟨i.val + 1, hi⟩ = true
  · simpa [fillOutgoing, fillIncoming, hc, hn] using h i hi hc hn
  all_goals simp [fillOutgoing, fillIncoming, hc, hn, hi]

private theorem fill_mem {n : ℕ} (carry : Fin n → Bool) (incoming outgoing : Fin n → ℕ)
    (colors : List ℕ) (hz : 0 ∈ colors)
    (hin : ∀ i, incoming i ∈ colors) (hout : ∀ i, outgoing i ∈ colors) (i : Fin n) :
    fillIncoming carry incoming outgoing i ∈ colors ∧
      fillOutgoing carry incoming outgoing i ∈ colors := by
  unfold fillIncoming fillOutgoing
  constructor <;> repeat' first | split | dsimp only | exact hin _ | exact hout _ | exact hz

private def addressedPayload {τ : List WangTile} (P : Plane τ) (role : RouteRole)
    (point horizontalSource verticalSource : ℤ × ℤ) : WangTile :=
  match role with
  | .active | .corner => P.tile point.1 point.2
  | .horizontal =>
    let c := (P.tile horizontalSource.1 horizontalSource.2).right
    ⟨0, 0, c, c⟩
  | .vertical =>
    let c := (P.tile verticalSource.1 verticalSource.2).top
    ⟨c, c, 0, 0⟩
  | .inactive => ⟨0, 0, 0, 0⟩

private theorem addressedPayload_mem {τ : List WangTile} (P : Plane τ) (r : RouteRole)
    (p h v : ℤ × ℤ) : addressedPayload P r p h v ∈ completePayloads τ := by
  have e (q : ℤ × ℤ) := mem_completePayloads.mp (mem_completePayloads_of_mem (P.mem q.1 q.2))
  have hz : 0 ∈ palette τ := List.mem_cons_self
  cases r <;> simp [addressedPayload, mem_completePayloads, e p, e h, e v, hz]

private def addressedRectangle {S : RoutedScaffold} {n : ℕ} (A : AddressedSquare S n)
    {I : SeededInstance} (P : Plane I.tiles) (seed : P.tile 0 0 = I.seed) :
    Rectangle (combine S I) (n + 1) (n + 1) := by
  let role i j := S.role (A.base.tile i j)
  let core i j := addressedPayload P (role i j)
    (A.point i j) (A.horizontalSource i j) (A.verticalSource i j)
  have core_mem i j := addressedPayload_mem P (role i j)
    (A.point i j) (A.horizontalSource i j) (A.verticalSource i j)
  have hmatch i j hi (hl : (role i j).horizontalCarrier = true)
      (hr : (role ⟨i.val + 1, hi⟩ j).horizontalCarrier = true) :
      (core i j).right = (core ⟨i.val + 1, hi⟩ j).left := by
    have step := A.hstep i j hi hl hr
    change (match role ⟨i.val + 1, hi⟩ j with
      | .active | .corner => A.point ⟨i.val + 1, hi⟩ j =
        (((role i j).horizontalOutgoing (A.point i j) (A.horizontalSource i j)).1 + 1,
          ((role i j).horizontalOutgoing (A.point i j) (A.horizontalSource i j)).2)
      | .horizontal => A.horizontalSource ⟨i.val + 1, hi⟩ j =
        (role i j).horizontalOutgoing (A.point i j) (A.horizontalSource i j)
      | _ => False) at step
    cases hleft : role i j <;> cases hright : role ⟨i.val + 1, hi⟩ j <;>
      simp_all only [Bool.false_eq_true, RouteRole.horizontalCarrier,
        RouteRole.horizontalOutgoing, core, addressedPayload]
    all_goals exact P.horizontal _ _
  have vmatch i j hj (hl : (role i j).verticalCarrier = true)
      (hr : (role i ⟨j.val + 1, hj⟩).verticalCarrier = true) :
      (core i j).top = (core i ⟨j.val + 1, hj⟩).bottom := by
    have step := A.vstep i j hj hl hr
    change (match role i ⟨j.val + 1, hj⟩ with
      | .active | .corner => A.point i ⟨j.val + 1, hj⟩ =
        (((role i j).verticalOutgoing (A.point i j) (A.verticalSource i j)).1,
          ((role i j).verticalOutgoing (A.point i j) (A.verticalSource i j)).2 + 1)
      | .vertical => A.verticalSource i ⟨j.val + 1, hj⟩ =
        (role i j).verticalOutgoing (A.point i j) (A.verticalSource i j)
      | _ => False) at step
    cases hlower : role i j <;> cases hupper : role i ⟨j.val + 1, hj⟩ <;>
      simp_all only [Bool.false_eq_true, RouteRole.verticalCarrier,
        RouteRole.verticalOutgoing, core, addressedPayload]
    all_goals exact P.vertical _ _
  let payload i j : WangTile :=
    ⟨fillOutgoing (fun k => (role i k).verticalCarrier)
        (fun k => (core i k).bottom) (fun k => (core i k).top) j,
      fillIncoming (fun k => (role i k).verticalCarrier)
        (fun k => (core i k).bottom) (fun k => (core i k).top) j,
      fillIncoming (fun k => (role k j).horizontalCarrier)
        (fun k => (core k j).left) (fun k => (core k j).right) i,
      fillOutgoing (fun k => (role k j).horizontalCarrier)
        (fun k => (core k j).left) (fun k => (core k j).right) i⟩
  have colors i j : payload i j ∈ completePayloads I.tiles := by
    have hc i j := mem_completePayloads.mp (core_mem i j)
    have hh := fill_mem (fun k => (role k j).horizontalCarrier)
      (fun k => (core k j).left) (fun k => (core k j).right)
      (palette I.tiles) List.mem_cons_self (fun k => (hc k j).2.2.1)
        (fun k => (hc k j).2.2.2) i
    have hv := fill_mem (fun k => (role i k).verticalCarrier)
      (fun k => (core i k).bottom) (fun k => (core i k).top)
      (palette I.tiles) List.mem_cons_self (fun k => (hc i k).2.1) (fun k => (hc i k).1) j
    exact mem_completePayloads.mpr ⟨hv.2, hv.1, hh.1, hh.2⟩
  have allowed i j : payload i j ∈ routedPayloads S I (A.base.tile i j) := by
    rw [mem_routedPayloads]
    change match role i j with
      | .inactive => payload i j ∈ completePayloads I.tiles
      | .horizontal => payload i j ∈ completePayloads I.tiles ∧
        (payload i j).left = (payload i j).right
      | .vertical => payload i j ∈ completePayloads I.tiles ∧
        (payload i j).bottom = (payload i j).top
      | .active => payload i j ∈ I.tiles
      | .corner => payload i j ∈ I.tiles ∧ payload i j = I.seed
    have crossing (hr : role i j = .active ∨ role i j = .corner) :
        payload i j = P.tile (A.point i j).1 (A.point i j).2 := by
      rcases hr with hr | hr <;>
        simp [payload, core, addressedPayload, hr, fillIncoming, fillOutgoing,
          RouteRole.horizontalCarrier, RouteRole.verticalCarrier]
    cases hr : role i j with
    | inactive => exact colors i j
    | horizontal =>
      exact ⟨colors i j, by simp [payload, core, addressedPayload, hr, fillIncoming,
        fillOutgoing, RouteRole.horizontalCarrier]⟩
    | vertical =>
      exact ⟨colors i j, by simp [payload, core, addressedPayload, hr, fillIncoming,
        fillOutgoing, RouteRole.verticalCarrier]⟩
    | active =>
      rw [crossing (Or.inl hr)]
      exact P.mem _ _
    | corner =>
      rw [crossing (Or.inr hr), A.corner_zero i j hr]
      exact ⟨P.mem 0 0, seed⟩
  refine {
    tile := fun i j => layer (A.base.tile i j) (payload i j)
    mem := fun i j => mem_combine.mpr
      ⟨A.base.tile i j, A.base.mem i j, payload i j, allowed i j, rfl⟩
    horizontal := ?_
    vertical := ?_ }
  · intro i j hi
    change Nat.pair _ _ = Nat.pair _ _
    rw [A.base.horizontal i j hi]
    exact congrArg (Nat.pair _) (fill_match (fun k => (role k j).horizontalCarrier)
      (fun k => (core k j).left) (fun k => (core k j).right) (fun k hk => hmatch k j hk) i hi)
  · intro i j hj
    change Nat.pair _ _ = Nat.pair _ _
    rw [A.base.vertical i j hj]
    exact congrArg (Nat.pair _) (fill_match (fun k => (role i k).verticalCarrier)
      (fun k => (core i k).bottom) (fun k => (core i k).top) (fun k hk => vmatch i k hk) j hj)

/-- Restrict a matching patch to a smaller rectangle at the same southwest corner. -/
def Rectangle.crop {τ : List WangTile} {w h w' h' : ℕ} (R : Rectangle τ w h)
    (hw : w' ≤ w) (hh : h' ≤ h) : Rectangle τ w' h' where
  tile i j := R.tile (i.castLE hw) (j.castLE hh)
  mem i j := R.mem (i.castLE hw) (j.castLE hh)
  horizontal i j hi := R.horizontal (i.castLE hw) (j.castLE hh) (lt_of_lt_of_le hi hw)
  vertical i j hj := R.vertical (i.castLE hw) (j.castLE hh) (lt_of_lt_of_le hj hh)

/-- Cofinal addressed squares realize every pointed payload plane. Flexible edges are filled
from neighboring carriers or zero, then ordinary finite-square compactness gives the plane. -/
theorem realizes_of_addressedSquares {S : RoutedScaffold}
    (squares : ∀ n, ∃ m, n ≤ m ∧ Nonempty (AddressedSquare S m)) : Realizes S := by
  rintro I ⟨f, hf, hm⟩
  refine (tilesPlane_iff_squares _).mpr fun n => ?_
  obtain ⟨m, hnm, ⟨A⟩⟩ := squares n
  exact ⟨(addressedRectangle A ⟨f, fun x y => (hm x y).1,
    fun x y => (hm x y).2.1, fun x y => (hm x y).2.2⟩ hf).crop (by omega) (by omega)⟩

/-- A generic seed-removal step, not the domino theorem: both geometric obligations remain
hypotheses. Finite extended squares decode to source squares, while a source quadrant extends
to the pointed plane required by realization. -/
theorem tilesPlane_combine_pointedExtension_iff_of_forces_of_realizes
    {S : RoutedScaffold} (forces : Forces S) (realizes : Realizes S) (I : SeededInstance) :
    TilesPlane (combine S (pointedExtension I)) ↔ TilesQuadrant I :=
  ⟨fun h => (tilesQuadrant_iff_seededSquares I).mpr fun n =>
      seededSquare_of_pointedExtension (forces _ h n),
    fun h => realizes _ ((tilesAtOrigin_pointedExtension_iff I).mpr h)⟩

end Cslib.WangTile
