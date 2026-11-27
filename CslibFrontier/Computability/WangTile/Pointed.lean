/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
import CslibFrontier.Computability.WangTile.Compactness

/-!
# Extending seeded quadrants to pointed planes

A finite position layer marks the two axes through a prescribed tile. The northeast quadrant
carries the source tiles, western rows transmit their left boundary colours, southern columns
transmit their bottom boundary colours, and the southwest region carries a zero filler.
Thus a seeded quadrant extends to a plane with a prescribed origin tile. Conversely, every
finite square rooted at the prescribed extension tile decodes to a source seeded square.
Compactness gives the infinite converse. The unseeded plane problem is a separate problem.

## Main definitions

* `Cslib.WangTile.pointedExtension`: nine regional variants of each source tile and a prescribed
  decorated seed.

## Main results

* `Cslib.WangTile.primrec_pointedExtension`: the instance transformation is primitive recursive.
* `Cslib.WangTile.tilesAtOrigin_pointedExtension_iff`: pointed extension preserves precisely
  seeded-quadrant tileability.
* `Cslib.WangTile.seededSquare_of_pointedExtension`: the finite-square decoding contract.

## References

This construction adapts [lean-wang, revision 64268a3, PointedExtension](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Scaffold/PointedExtension.lean).
Unlike that palette, all source tiles are allowed in the origin region: the prescribed tile
already fixes its payload. Each source tile also contributes a southwest filler copy, so an
empty source palette has an empty extension. Neither change alters the pointed or finite
seeded-square contracts.
-/

public section

namespace Cslib.WangTile

namespace Pointed

/-- The position of one coordinate relative to its distinguished axis. -/
private inductive Axis where
  | negative | origin | positive
  deriving DecidableEq

private def Axis.before : Axis → ℕ
  | .negative | .origin => 0
  | .positive => 1

private def Axis.after : Axis → ℕ
  | .negative => 0
  | .origin | .positive => 1

private def Axis.code : Axis → ℕ
  | .negative => 0
  | .origin => 1
  | .positive => 2

private theorem Axis.code_inj {a b : Axis} : a.code = b.code ↔ a = b := by
  cases a <;> cases b <;> simp [code]

/-- Each edge pairs its axis-transition and perpendicular-axis tags with the payload colour. -/
private def decorate (x y : Axis) (t : WangTile) : WangTile where
  top := Nat.pair (Nat.pair y.after x.code) t.top
  bottom := Nat.pair (Nat.pair y.before x.code) t.bottom
  left := Nat.pair (Nat.pair x.before y.code) t.left
  right := Nat.pair (Nat.pair x.after y.code) t.right

private theorem decorate_horizontal {x y x' y' : Axis} {t t' : WangTile} :
    (decorate x y t).right = (decorate x' y' t').left ↔
      x.after = x'.before ∧ y = y' ∧ t.right = t'.left := by
  simp [decorate, Nat.pair_eq_pair, Axis.code_inj, and_assoc]

private theorem decorate_vertical {x y x' y' : Axis} {t t' : WangTile} :
    (decorate x y t).top = (decorate x' y' t').bottom ↔
      y.after = y'.before ∧ x = x' ∧ t.top = t'.bottom := by
  simp [decorate, Nat.pair_eq_pair, Axis.code_inj, and_assoc]

private theorem decorate_inj {x y x' y' : Axis} {t t' : WangTile} :
    decorate x y t = decorate x' y' t' ↔ x = x' ∧ y = y' ∧ t = t' := by
  cases t
  cases t'
  simp [decorate, Nat.pair_eq_pair, Axis.code_inj, WangTile.mk.injEq]
  tauto

private def horizontalWire (t : WangTile) : WangTile := ⟨0, 0, t.left, t.left⟩

private def verticalWire (t : WangTile) : WangTile := ⟨t.bottom, t.bottom, 0, 0⟩

/-- The source tile is retained in the northeast, with wires and filler elsewhere. -/
private def payload : Axis → Axis → WangTile → WangTile
  | .negative, .negative, _ => ⟨0, 0, 0, 0⟩
  | .negative, _, t => horizontalWire t
  | _, .negative, t => verticalWire t
  | _, _, t => t

private def variants (t : WangTile) : List WangTile :=
  [decorate .negative .negative (payload .negative .negative t),
    decorate .negative .origin (payload .negative .origin t),
    decorate .negative .positive (payload .negative .positive t),
    decorate .origin .negative (payload .origin .negative t),
    decorate .origin .origin t,
    decorate .origin .positive t,
    decorate .positive .negative (payload .positive .negative t),
    decorate .positive .origin t,
    decorate .positive .positive t]

private theorem mem_variants {s t : WangTile} :
    s ∈ variants t ↔ ∃ x y, decorate x y (payload x y t) = s := by
  constructor
  · simp only [variants, List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | exact ⟨.negative, .negative, rfl⟩
                    | exact ⟨.negative, .origin, rfl⟩
                    | exact ⟨.negative, .positive, rfl⟩
                    | exact ⟨.origin, .negative, rfl⟩
                    | exact ⟨.origin, .origin, rfl⟩
                    | exact ⟨.origin, .positive, rfl⟩
                    | exact ⟨.positive, .negative, rfl⟩
                    | exact ⟨.positive, .origin, rfl⟩
                    | exact ⟨.positive, .positive, rfl⟩
  · rintro ⟨x, y, rfl⟩
    cases x <;> cases y <;> simp [variants, payload]

private theorem primrec_decorate (x y : Axis) : Primrec (decorate x y) :=
  primrec_mk (Primrec₂.natPair.comp (.const _) primrec_top)
    (Primrec₂.natPair.comp (.const _) primrec_bottom)
    (Primrec₂.natPair.comp (.const _) primrec_left)
    (Primrec₂.natPair.comp (.const _) primrec_right)

private theorem primrec_payload (x y : Axis) : Primrec (payload x y) := by
  have hw : Primrec horizontalWire :=
    primrec_mk (.const 0) (.const 0) primrec_left primrec_left
  have hv : Primrec verticalWire :=
    primrec_mk primrec_bottom primrec_bottom (.const 0) (.const 0)
  cases x with
  | negative =>
      cases y with
      | negative => exact .const _
      | origin | positive => exact hw
  | origin | positive =>
      cases y with
      | negative => exact hv
      | origin | positive => exact Primrec.id

private theorem primrec_variants : Primrec variants := by
  have h (x y : Axis) : Primrec fun t => decorate x y (payload x y t) :=
    (primrec_decorate x y).comp (primrec_payload x y)
  exact Primrec.list_cons.comp (h .negative .negative)
    (Primrec.list_cons.comp (h .negative .origin)
      (Primrec.list_cons.comp (h .negative .positive)
        (Primrec.list_cons.comp (h .origin .negative)
          (Primrec.list_cons.comp (h .origin .origin)
            (Primrec.list_cons.comp (h .origin .positive)
              (Primrec.list_cons.comp (h .positive .negative)
                (Primrec.list_cons.comp (h .positive .origin)
                  (Primrec.list_cons.comp (h .positive .positive) (.const [])))))))))

end Pointed

/-- Extend a seeded quadrant instance to a pointed plane instance. The palette contains nine
regional variants per source tile, with duplicates retained: southwest filler; western wires;
southern wires; and the original payload in each northeast region, including the origin. The
prescribed seed is the source seed decorated with two origin tags. An empty source palette
has an empty extension palette. -/
def pointedExtension (I : SeededInstance) : SeededInstance where
  tiles := I.tiles.flatMap Pointed.variants
  seed := Pointed.decorate .origin .origin I.seed

/-- The transformation from seeded quadrants to pointed planes is primitive recursive. -/
theorem primrec_pointedExtension : Primrec pointedExtension :=
  SeededInstance.primrec₂_mk.comp
    (Primrec.list_flatMap SeededInstance.primrec_tiles
      ((Pointed.primrec_variants.comp Primrec.snd).to₂))
    ((Pointed.primrec_decorate .origin .origin).comp SeededInstance.primrec_seed)

namespace Pointed

/-- The source tile and the two axis classes witnessing membership in the extension palette. -/
private structure Decoded (I : SeededInstance) (t : WangTile) where
  /-- The horizontal position class. -/
  horizontal : Axis
  /-- The vertical position class. -/
  vertical : Axis
  /-- A source tile whose regional variant is `t`. -/
  source : WangTile
  /-- The source tile belongs to the source palette. -/
  source_mem : source ∈ I.tiles
  /-- Decorating the regional payload gives the extension tile. -/
  tile_eq : decorate horizontal vertical (payload horizontal vertical source) = t

private def Decoded.payload {I : SeededInstance} {t : WangTile} (d : Decoded I t) :
    WangTile := Pointed.payload d.horizontal d.vertical d.source

private theorem decoded_of_mem {I : SeededInstance} {t : WangTile}
    (h : t ∈ (pointedExtension I).tiles) : Nonempty (Decoded I t) := by
  obtain ⟨source, hm, hs⟩ := List.mem_flatMap.mp h
  obtain ⟨x, y, heq⟩ := mem_variants.mp hs
  exact ⟨⟨x, y, source, hm, heq⟩⟩

private theorem Decoded.horizontal_match {I : SeededInstance} {t u : WangTile}
    (d : Decoded I t) (e : Decoded I u) (h : t.right = u.left) :
    d.horizontal.after = e.horizontal.before ∧ d.vertical = e.vertical ∧
      d.payload.right = e.payload.left := by
  rw [← d.tile_eq, ← e.tile_eq] at h
  exact decorate_horizontal.mp h

private theorem Decoded.vertical_match {I : SeededInstance} {t u : WangTile}
    (d : Decoded I t) (e : Decoded I u) (h : t.top = u.bottom) :
    d.vertical.after = e.vertical.before ∧ d.horizontal = e.horizontal ∧
      d.payload.top = e.payload.bottom := by
  rw [← d.tile_eq, ← e.tile_eq] at h
  exact decorate_vertical.mp h

private theorem payload_of_nonnegative {x y : Axis} (hx : x ≠ .negative)
    (hy : y ≠ .negative) (t : WangTile) : payload x y t = t := by
  cases x <;> cases y <;> simp_all [payload]

private theorem Axis.nonnegative_of_step {a b : Axis}
    (h : a.after = b.before) (ha : a ≠ .negative) : b ≠ .negative := by
  cases a <;> cases b <;> simp_all [after, before]

private theorem axisGrid_nonnegative {n : ℕ} (grid : Fin (n + 1) → Fin (n + 1) → Axis)
    (origin : grid 0 0 = .origin)
    (along : ∀ i : Fin n, (grid i.castSucc 0).after = (grid i.succ 0).before)
    (across : ∀ i (j : Fin n), grid i j.castSucc = grid i j.succ) :
    ∀ i j, grid i j ≠ .negative := by
  have hbottom : ∀ i, grid i 0 ≠ .negative :=
    Fin.induction (by simp [origin])
      (fun i ih => Axis.nonnegative_of_step (along i) ih)
  intro i
  exact Fin.induction (hbottom i) (fun j ih => by rwa [← across i j])

end Pointed

/-- Every finite square of the extension rooted at its prescribed tile decodes to a source
square of the same side length. This is the finite contract needed when removing the seed. -/
theorem seededSquare_of_pointedExtension {I : SeededInstance} {n : ℕ} :
    Nonempty (SeededSquare (pointedExtension I) n) → Nonempty (SeededSquare I n) := by
  classical
  rintro ⟨q⟩
  let d (i j : Fin (n + 1)) : Pointed.Decoded I (q.tile i j) :=
    Classical.choice (Pointed.decoded_of_mem (q.mem i j))
  have corner := Pointed.decorate_inj.mp ((d 0 0).tile_eq.trans q.corner)
  have hx (i j : Fin (n + 1)) : (d i j).horizontal ≠ .negative := by
    apply Pointed.axisGrid_nonnegative (fun i j => (d i j).horizontal) corner.1
    · intro k
      exact ((d k.castSucc 0).horizontal_match (d k.succ 0)
        (q.horizontal k.castSucc 0 k.succ.isLt)).1
    · intro i k
      exact ((d i k.castSucc).vertical_match (d i k.succ)
        (q.vertical i k.castSucc k.succ.isLt)).2.1
  have hy (i j : Fin (n + 1)) : (d i j).vertical ≠ .negative := by
    apply Pointed.axisGrid_nonnegative (fun j i => (d i j).vertical) corner.2.1
    · intro k
      exact ((d 0 k.castSucc).vertical_match (d 0 k.succ)
        (q.vertical 0 k.castSucc k.succ.isLt)).1
    · intro j k
      exact ((d k.castSucc j).horizontal_match (d k.succ j)
        (q.horizontal k.castSucc j k.succ.isLt)).2.1
  refine ⟨{
    tile := fun i j => (d i j).payload
    mem := ?_
    horizontal := ?_
    vertical := ?_
    corner := corner.2.2 }⟩
  · intro i j
    rw [Pointed.Decoded.payload, Pointed.payload_of_nonnegative (hx i j) (hy i j)]
    exact (d i j).source_mem
  · intro i j hi
    exact ((d i j).horizontal_match (d ⟨i.val + 1, hi⟩ j) (q.horizontal i j hi)).2.2
  · intro i j hj
    exact ((d i j).vertical_match (d i ⟨j.val + 1, hj⟩) (q.vertical i j hj)).2.2

namespace Pointed

private def classOfInt (z : ℤ) : Axis :=
  if z < 0 then .negative else if z = 0 then .origin else .positive

private theorem classOfInt_step (z : ℤ) :
    (classOfInt z).after = (classOfInt (z + 1)).before := by
  unfold classOfInt
  split_ifs <;> simp_all [Axis.after, Axis.before] <;> omega

private def westPayload (f : ℕ → ℕ → WangTile) (row : ℕ) (x : ℤ) : WangTile :=
  if 0 ≤ x then f x.toNat row else horizontalWire (f 0 row)

private def planePayload (f : ℕ → ℕ → WangTile) (x y : ℤ) : WangTile :=
  if 0 ≤ y then westPayload f y.toNat x else verticalWire (westPayload f 0 x)

private theorem payload_class (x y : ℤ) (t : WangTile) :
    payload (classOfInt x) (classOfInt y) t =
      if 0 ≤ y then (if 0 ≤ x then t else horizontalWire t)
      else verticalWire (if 0 ≤ x then t else horizontalWire t) := by
  unfold classOfInt
  split_ifs <;> simp_all [payload, horizontalWire, verticalWire] <;> omega

private theorem planePayload_eq (f : ℕ → ℕ → WangTile) (x y : ℤ) :
    planePayload f x y = payload (classOfInt x) (classOfInt y) (f x.toNat y.toNat) := by
  rw [payload_class]
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · simp [planePayload, westPayload, hx, hy]
  · simp [planePayload, westPayload, hx, hy, Int.toNat_eq_zero.mpr (by omega : y ≤ 0)]
  · simp [planePayload, westPayload, hx, hy, Int.toNat_eq_zero.mpr (by omega : x ≤ 0)]
  · simp [planePayload, westPayload, hx, hy, horizontalWire, verticalWire]

private theorem westPayload_horizontal (f : ℕ → ℕ → WangTile)
    (h : ∀ x y, (f x y).right = (f (x + 1) y).left) (row : ℕ) (x : ℤ) :
    (westPayload f row x).right = (westPayload f row (x + 1)).left := by
  by_cases hx : 0 ≤ x
  · have hx' : 0 ≤ x + 1 := by omega
    simpa [westPayload, hx, hx', Int.toNat_add hx (by decide : (0 : ℤ) ≤ 1)] using h x.toNat row
  · by_cases hx' : 0 ≤ x + 1
    · have hb : x + 1 = 0 := by omega
      simp [westPayload, hx, hb, horizontalWire]
    · simp [westPayload, hx, hx', horizontalWire]

private theorem planePayload_horizontal (f : ℕ → ℕ → WangTile)
    (h : ∀ x y, (f x y).right = (f (x + 1) y).left) (x y : ℤ) :
    (planePayload f x y).right = (planePayload f (x + 1) y).left := by
  by_cases hy : 0 ≤ y
  · simpa [planePayload, hy] using westPayload_horizontal f h y.toNat x
  · simp [planePayload, hy, verticalWire]

private theorem planePayload_vertical (f : ℕ → ℕ → WangTile)
    (h : ∀ x y, (f x y).top = (f x (y + 1)).bottom) (x y : ℤ) :
    (planePayload f x y).top = (planePayload f x (y + 1)).bottom := by
  by_cases hy : 0 ≤ y
  · have hy' : 0 ≤ y + 1 := by omega
    by_cases hx : 0 ≤ x
    · simpa [planePayload, westPayload, hx, hy, hy',
        Int.toNat_add hy (by decide : (0 : ℤ) ≤ 1)] using h x.toNat y.toNat
    · simp [planePayload, westPayload, hx, hy, hy', horizontalWire]
  · by_cases hy' : 0 ≤ y + 1
    · have hb : y + 1 = 0 := by omega
      simp [planePayload, hy, hb, verticalWire]
    · simp [planePayload, hy, hy', verticalWire]

end Pointed

/-- A plane tiled by the pointed extension with its prescribed tile at the origin exists
exactly when the source seeded quadrant is tileable. No seed-membership assumption is needed. -/
theorem tilesAtOrigin_pointedExtension_iff (I : SeededInstance) :
    TilesAtOrigin (pointedExtension I) ↔ TilesQuadrant I := by
  constructor
  · rintro ⟨f, hseed, hf⟩
    apply (tilesQuadrant_iff_seededSquares I).mpr
    intro n
    apply seededSquare_of_pointedExtension
    exact ⟨{
      tile := fun i j => f i.val j.val
      mem := fun i j => (hf i.val j.val).1
      horizontal := fun i j hi => by simpa using (hf i.val j.val).2.1
      vertical := fun i j hj => by simpa using (hf i.val j.val).2.2
      corner := hseed }⟩
  · rintro ⟨f, hseed, hf⟩
    refine ⟨fun x y => Pointed.decorate (Pointed.classOfInt x) (Pointed.classOfInt y)
      (Pointed.planePayload f x y), ?_, ?_⟩
    · change Pointed.decorate .origin .origin (f 0 0) = Pointed.decorate .origin .origin I.seed
      exact congrArg (Pointed.decorate .origin .origin) hseed
    · intro x y
      refine ⟨?_, ?_, ?_⟩
      · apply List.mem_flatMap.mpr
        refine ⟨f x.toNat y.toNat, (hf _ _).1, Pointed.mem_variants.mpr ?_⟩
        exact ⟨Pointed.classOfInt x, Pointed.classOfInt y,
          congrArg (Pointed.decorate _ _) (Pointed.planePayload_eq f x y).symm⟩
      · exact Pointed.decorate_horizontal.mpr
          ⟨Pointed.classOfInt_step x, rfl,
            Pointed.planePayload_horizontal f (fun x y => (hf x y).2.1) x y⟩
      · exact Pointed.decorate_vertical.mpr
          ⟨Pointed.classOfInt_step y, rfl,
            Pointed.planePayload_vertical f (fun x y => (hf x y).2.2) x y⟩

end Cslib.WangTile
