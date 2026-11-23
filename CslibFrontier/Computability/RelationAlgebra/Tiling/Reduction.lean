/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationAlgebra.Tiling.TilingOfWinning
public import CslibFrontier.Computability.RelationAlgebra.Tiling.WinningOfTiling
public import CslibFrontier.Foundations.RelationAlgebra.AtomTable
public import CslibFrontier.Foundations.RelationAlgebra.Finite
public import Mathlib.Computability.Reduce

/-!
# From tilings to representability of finite relation algebras

The reduction of [HirschHodkinson2001]: a list `τ` of Wang tiles is sent to the table of the
algebra `RA(τ⁺)`, where `τ⁺` is `τ` with a fresh special tile in front, and every tile of `τ` is
at the origin of a tiling by `τ` if and only if that table presents an atom structure whose
complex algebra is representable.

The table is computed from the tiles by arithmetic on the numbers of the atoms
(`Tiling.Atom.code`), so that the map is primitive recursive. A table that presents an atom
structure presents the frame `tilingFrame`, with its atoms numbered. When `RA(τ⁺)` is not
associative its table presents no atom structure, and such a list is a no-instance on both sides,
as in the source, where a non-associative `RA(τ)` is treated as a no-instance.

## Main definitions

* `Cslib.RelationAlgebra.tilingTable`: the table of `RA(τ)` for a list of tiles.

## Main results

* `Cslib.RelationAlgebra.presents_tilingTable_iff`: the atom structures that the table of `RA(τ)`
  presents are those whose frame is `tilingFrame`, with the atoms numbered.
* `Cslib.RelationAlgebra.isRepresentable_tilingTable_iff`: the table of `RA(τ)` presents an atom
  structure with a representable complex algebra if and only if ∃ has a winning strategy in the
  game on `tilingFrame`. This uses Theorem 1 and Lemma 7 of the source.
* `Cslib.RelationAlgebra.computable_tilingTable_cons_freshTile`: the reduction is computable.
* `Cslib.RelationAlgebra.everyTileOccurs_iff_isRepresentable`: the reduction is correct, by
  Theorems 3 and 4 of the source.
* `Cslib.RelationAlgebra.everyTileOccurs_manyOneReducible_isRepresentable`: the tiling problem
  many-one reduces to the representation problem for tables. This is a reduction; it does not
  say that either problem is undecidable.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

namespace Cslib.RelationAlgebra

open WangTile Tiling Tiling.Atom

namespace Tiling

/-! ### The frame of `RA(τ)` on the numbers of the atoms -/

/-- The number of the converse of the atom numbered `a`. -/
@[expose] def convCode (a : ℕ) : ℕ :=
  if a < 12 then [0, 1, 2, 3, 6, 9, 4, 7, 10, 5, 8, 11].getD a 0
  else if a % 2 = 0 then a + 1 else a - 1

/-- The number of the kind of node at which the edges of the atom numbered `a` start. -/
@[expose] def srcCode (a : ℕ) : ℕ :=
  if a < 28 then
    [0, 1, 2, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2].getD a 0
  else 1 + a % 2

/-- The tile of the tile atom numbered `a`. -/
@[expose] def tileOfCode (L : List WangTile) (a : ℕ) : WangTile :=
  L.getD ((a - 28) / 2) ⟨0, 0, 0, 0⟩

/-- `Rule` on the numbers of atoms: the seven rules in the order of `Rule`. -/
@[expose] def RuleCode (L : List WangTile) (a b c : ℕ) : Prop :=
  (a = 17 ∧ b = 18 ∧ c = 8) ∨
  (28 ≤ a ∧ a % 2 = 0 ∧ 28 ≤ b ∧ b % 2 = 1 ∧ c = 13 ∧
    (tileOfCode L a).left ≠ (tileOfCode L b).right) ∨
  (28 ≤ a ∧ a % 2 = 1 ∧ 28 ≤ b ∧ b % 2 = 0 ∧ c = 15 ∧
    (tileOfCode L a).bottom ≠ (tileOfCode L b).top) ∨
  (a = 21 ∧ b = 18 ∧ 30 ≤ c ∧ c % 2 = 0) ∨
  (a = 23 ∧ b = 16 ∧ 31 ≤ c ∧ c % 2 = 1) ∨
  (a = 25 ∧ b = 16 ∧ (c = 12 ∨ c = 13)) ∨
  (a = 27 ∧ b = 18 ∧ (c = 14 ∨ c = 15))

instance (L : List WangTile) (a b c : ℕ) : Decidable (RuleCode L a b c) := by
  unfold RuleCode
  infer_instance

/-- `Forbidden` on the numbers of atoms. -/
@[expose] def ForbiddenCode (L : List WangTile) (a b c : ℕ) : Prop :=
  RuleCode L a b c ∨ RuleCode L b (convCode c) (convCode a) ∨
    RuleCode L (convCode c) a (convCode b) ∨ RuleCode L (convCode a) c b ∨
    RuleCode L c (convCode b) a ∨ RuleCode L (convCode b) (convCode a) (convCode c)

instance (L : List WangTile) (a b c : ℕ) : Decidable (ForbiddenCode L a b c) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `Cycle` on the numbers of atoms. -/
@[expose] def CycleCode (L : List WangTile) (a b c : ℕ) : Prop :=
  srcCode (convCode a) = srcCode b ∧ srcCode a = srcCode c ∧
    srcCode (convCode b) = srcCode (convCode c) ∧ (a < 3 → c = b) ∧ (b < 3 → c = a) ∧
    (c < 3 → b = convCode a) ∧ ¬ForbiddenCode L a b c

instance (L : List WangTile) (a b c : ℕ) : Decidable (CycleCode L a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {k : ℕ} {L : List WangTile}

private theorem code_conv (a : Atom (Fin k)) : a.conv.code = convCode a.code := by
  have tile (i : ℕ) : convCode (28 + 2 * i) = 28 + 2 * i + 1 ∧
      convCode (28 + 2 * i + 1) = 28 + 2 * i := by
    unfold convCode
    constructor <;> split_ifs <;> omega
  rcases a with (_ | _ | _) | ⟨_ | _ | _, _ | _ | _⟩ | ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ |
    ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ | ⟨i, _ | _⟩
  case tile.forward => exact (tile i).1.symm
  case tile.reverse => exact (tile i).2.symm
  all_goals simp [Atom.conv, Atom.code, convCode, Direction.flip, Kind.toNat, Axis.toNat,
    Direction.toNat]

private theorem toNat_src (a : Atom (Fin k)) : a.src.toNat = srcCode a.code := by
  have tile (i : ℕ) : srcCode (28 + 2 * i) = 1 ∧ srcCode (28 + 2 * i + 1) = 2 := by
    unfold srcCode
    constructor <;> split_ifs <;> omega
  rcases a with (_ | _ | _) | ⟨_ | _ | _, _ | _ | _⟩ | ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ |
    ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ | ⟨i, _ | _⟩
  case tile.forward => exact (tile i).1.symm
  case tile.reverse => exact (tile i).2.symm
  all_goals simp [Atom.src, Atom.code, srcCode, Axis.kind, Kind.toNat, Axis.toNat,
    Direction.toNat]

private theorem isUnit_iff_code_lt (a : Atom (Fin k)) : a.IsUnit ↔ a.code < 3 := by
  rcases a with (_ | _ | _) | ⟨_ | _ | _, _ | _ | _⟩ | ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ |
    ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ | ⟨i, _ | _⟩
  case tile.forward | tile.reverse =>
    exact iff_of_false id (by simp only [Atom.code, Direction.toNat]; omega)
  all_goals simp [Atom.IsUnit, Atom.code, Kind.toNat, Axis.toNat, Direction.toNat]

private theorem exists_eq_tile_of_le_code {a : Atom (Fin k)} (h : 28 ≤ a.code) :
    ∃ i o, a = tile i o := by
  rcases a with (_ | _ | _) | ⟨_ | _ | _, _ | _ | _⟩ | ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ |
    ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ | ⟨i, o⟩
  case tile => exact ⟨i, o, rfl⟩
  all_goals simp [Atom.code, Kind.toNat, Axis.toNat, Direction.toNat] at h

private theorem tileOfCode_code (i : Fin L.length) (o : Direction) :
    tileOfCode L (tile i o).code = L[i] := by
  have : (28 + 2 * i.val + o.toNat - 28) / 2 = i := by
    cases o <;> simp only [Direction.toNat] <;> omega
  simp [tileOfCode, Atom.code, this]

private theorem ruleCode_code (r s t : Atom (Fin L.length)) :
    RuleCode L r.code s.code t.code ↔ Rule L r s t := by
  unfold Rule
  split
  case h_8 h₁ h₂ h₃ h₄ h₅ h₆ h₇ =>
    have eq (x : Atom (Fin L.length)) {y : Atom (Fin L.length)} {n : ℕ} (hx : x.code = n)
        (hy : y.code = n) : y = x := code_injective (hy.trans hx.symm)
    refine iff_false_intro ?_
    rintro (⟨hr, hs, ht⟩ | ⟨hr, hr', hs, hs', ht, -⟩ | ⟨hr, hr', hs, hs', ht, -⟩ |
      ⟨hr, hs, ht, ht'⟩ | ⟨hr, hs, ht, ht'⟩ | ⟨hr, hs, ht | ht⟩ | ⟨hr, hs, ht | ht⟩)
    · exact h₁ (eq (green .one .reverse) rfl hr) (eq (green .two .forward) rfl hs)
        (eq (white .one .two) rfl ht)
    · obtain ⟨i, _ | _, rfl⟩ := exists_eq_tile_of_le_code hr <;>
        obtain ⟨j, _ | _, rfl⟩ := exists_eq_tile_of_le_code hs <;>
        simp only [Atom.code, Direction.toNat] at hr' hs' <;> first
          | exact h₂ i j rfl rfl (eq (step .one .reverse) rfl ht)
          | omega
    · obtain ⟨i, _ | _, rfl⟩ := exists_eq_tile_of_le_code hr <;>
        obtain ⟨j, _ | _, rfl⟩ := exists_eq_tile_of_le_code hs <;>
        simp only [Atom.code, Direction.toNat] at hr' hs' <;> first
          | exact h₃ i j rfl rfl (eq (step .two .reverse) rfl ht)
          | omega
    · obtain ⟨i, _ | _, rfl⟩ := exists_eq_tile_of_le_code (show 28 ≤ t.code by omega)
      · exact h₄ i (eq (u .one .reverse) rfl hr) (eq (green .two .forward) rfl hs) rfl
      · simp only [Atom.code, Direction.toNat] at ht'
        omega
    · obtain ⟨i, _ | _, rfl⟩ := exists_eq_tile_of_le_code (show 28 ≤ t.code by omega)
      · simp only [Atom.code, Direction.toNat] at ht'
        omega
      · exact h₅ i (eq (u .two .reverse) rfl hr) (eq (green .one .forward) rfl hs) rfl
    · exact h₆ .forward (eq (v .one .reverse) rfl hr) (eq (green .one .forward) rfl hs)
        (eq (step .one .forward) rfl ht)
    · exact h₆ .reverse (eq (v .one .reverse) rfl hr) (eq (green .one .forward) rfl hs)
        (eq (step .one .reverse) rfl ht)
    · exact h₇ .forward (eq (v .two .reverse) rfl hr) (eq (green .two .forward) rfl hs)
        (eq (step .two .forward) rfl ht)
    · exact h₇ .reverse (eq (v .two .reverse) rfl hr) (eq (green .two .forward) rfl hs)
        (eq (step .two .reverse) rfl ht)
  case h_1 => simp [RuleCode, Atom.code, Kind.toNat, Axis.toNat, Direction.toNat]
  case h_6 | h_7 =>
    rename_i o
    cases o <;> simp [RuleCode, Atom.code, Axis.toNat, Direction.toNat]
  all_goals
    simp only [RuleCode, tileOfCode_code]
    simp [Atom.code, Axis.toNat, Direction.toNat]
    omega

private theorem cycleCode_code (r s t : Atom (Fin L.length)) :
    CycleCode L r.code s.code t.code ↔ Cycle L r s t := by
  have toNat_injective : Function.Injective Kind.toNat := by
    rintro (_ | _ | _) (_ | _ | _) <;> simp [Kind.toNat]
  simp only [CycleCode, ForbiddenCode, ← code_conv, ← toNat_src, ruleCode_code,
    toNat_injective.eq_iff, ← isUnit_iff_code_lt, code_injective.eq_iff, cycle_iff, Forbidden,
    Atom.tgt]

end Tiling

/-! ### The table -/

/-- The table of the algebra `RA(τ)` of [HirschHodkinson2001], Section 4, for the tiles listed in
`L`: the frame `tilingFrame L` with its atoms numbered by `Tiling.Atom.code`. It has `2k + 28`
atoms for `k` tiles; the atoms `0`, `1`, `2` are the identity atoms, and the cycles are the
triples of atoms that satisfy `Tiling.CycleCode`, in lexicographic order. -/
@[expose] def tilingTable (L : List WangTile) : AtomTable :=
  let atoms := List.range (2 * L.length + 28)
  { size := 2 * L.length + 28
    conv := atoms.map convCode
    id := [0, 1, 2]
    cycles := (atoms.flatMap fun a => atoms.flatMap fun b => atoms.map fun c => (a, b, c)).filter
      fun (a, b, c) => CycleCode L a b c }

variable {L : List WangTile}

/-- The table of `RA(τ)` presents an atom structure exactly when that structure, with its atoms
renamed back along the numbering `Tiling.Atom.equivFin`, is `tilingFrame L`: the
converse list, the identity list and the cycle list of the table are the converse, the units and
the consistent triangles of `RA(τ)` on the numbers of the atoms. -/
theorem presents_tilingTable_iff (A : AtomStructure (Fin (2 * L.length + 28))) :
    (tilingTable L).Presents A ↔ A.map equivFin.symm = tilingFrame L := by
  have hconv (a : Atom (Fin L.length)) :
      (tilingTable L).conv[(equivFin a : ℕ)]? = some (equivFin a.conv : ℕ) := by
    simp [tilingTable, a.code_lt, code_conv]
  have hid (a : Atom (Fin L.length)) : (equivFin a : ℕ) ∈ (tilingTable L).id ↔ a.IsUnit := by
    rw [isUnit_iff_code_lt, coe_equivFin]
    simp only [tilingTable, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hcycles (r s t : Atom (Fin L.length)) : ((equivFin r : ℕ), (equivFin s : ℕ),
      (equivFin t : ℕ)) ∈ (tilingTable L).cycles ↔ Cycle L r s t := by
    simp [tilingTable, code_lt, cycleCode_code]
  constructor
  · intro h
    have h₁ : (A.map equivFin.symm).conv = Atom.conv := by
      funext a
      apply equivFin.injective
      apply Fin.ext
      simpa using (h.conv (equivFin a)).symm.trans (hconv a)
    have h₂ : (A.map equivFin.symm).id = {a | a.IsUnit} := Set.ext fun a =>
      (h.id (equivFin a)).trans (hid a)
    have h₃ : (A.map equivFin.symm).cycles = {(r, s, t) | Cycle L r s t} := Set.ext
      fun ⟨r, s, t⟩ => (h.cycles (equivFin r) (equivFin s) (equivFin t)).trans (hcycles r s t)
    rw [tilingFrame, ← h₁, ← h₂, ← h₃]
  · intro h
    have h₁ (a : Atom (Fin L.length)) : A.conv (equivFin a) = equivFin a.conv :=
      equivFin.symm_apply_eq.mp (congrFun (congrArg AtomStructure.conv h) a)
    have h₂ (a : Atom (Fin L.length)) : equivFin a ∈ A.id ↔ a.IsUnit :=
      iff_of_eq (congrArg (a ∈ ·) (congrArg AtomStructure.id h))
    have h₃ (r s t : Atom (Fin L.length)) :
        (equivFin r, equivFin s, equivFin t) ∈ A.cycles ↔ Cycle L r s t :=
      iff_of_eq (congrArg ((r, s, t) ∈ ·) (congrArg AtomStructure.cycles h))
    refine ⟨fun a => ?_, fun a => ?_, fun a b c => ?_⟩
    · obtain ⟨a, rfl⟩ := equivFin.surjective a
      rw [h₁]
      exact hconv a
    · obtain ⟨a, rfl⟩ := equivFin.surjective a
      exact (h₂ a).trans (hid a).symm
    · obtain ⟨a, rfl⟩ := equivFin.surjective a
      obtain ⟨b, rfl⟩ := equivFin.surjective b
      obtain ⟨c, rfl⟩ := equivFin.surjective c
      exact (h₃ a b c).trans (hcycles a b c).symm

/-- The table of `RA(τ)` presents a lawful atom structure whose complex algebra is representable
if and only if ∃ has a winning strategy in the game on `RA(τ)`. From left to right this is
Theorem 1 of [HirschHodkinson2001]. From right to left, `RA(τ)` satisfies the laws by Lemma 7, the
table presents it, and its complex algebra is representable by Theorem 1. -/
theorem isRepresentable_tilingTable_iff :
    (tilingTable L).IsRepresentable ↔ (tilingFrame L).HasWinningStrategy := by
  -- The table has `2 * L.length + 28` atoms by definition; stating it so lets instance search
  -- match the atom type of `equivFin`.
  change (∃ A : AtomStructure (Fin (2 * L.length + 28)), (tilingTable L).Presents A ∧
    ∃ _ : LawfulAtomStructure A, Representable (ComplexAlgebra A)) ↔ _
  constructor
  · rintro ⟨A, hA, _, hrep⟩
    rw [← (presents_tilingTable_iff A).mp hA]
    exact (representable_complexAlgebra_iff _).mp
      ((ComplexAlgebra.mapEquiv A equivFin.symm).representable_iff.mp hrep)
  · intro h
    have := h.lawful
    exact ⟨(tilingFrame L).map equivFin,
      (presents_tilingTable_iff _).mpr ((tilingFrame L).map_map_symm equivFin), inferInstance,
      (ComplexAlgebra.mapEquiv _ equivFin).representable_iff.mp
        ((representable_complexAlgebra_iff _).mpr h)⟩

/-! ### The reduction -/

private theorem primrec_convCode : Primrec convCode :=
  Primrec.ite (Primrec.nat_lt.comp .id (.const 12))
    ((Primrec.list_getD 0).comp (.const _) .id)
    (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp .id (.const 2)) (.const 0)) .succ
      (Primrec.nat_sub.comp .id (.const 1)))

private theorem primrec_srcCode : Primrec srcCode :=
  Primrec.ite (Primrec.nat_lt.comp .id (.const 28))
    ((Primrec.list_getD 0).comp (.const _) .id)
    (Primrec.nat_add.comp (.const 1) (Primrec.nat_mod.comp .id (.const 2)))

private theorem primrecPred_ruleCode {α : Type*} [Primcodable α] {f : α → List WangTile}
    {a b c : α → ℕ} (hf : Primrec f) (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    PrimrecPred fun x => RuleCode (f x) (a x) (b x) (c x) := by
  have eq {g : α → ℕ} (hg : Primrec g) (n : ℕ) : PrimrecPred fun x => g x = n :=
    Primrec.eq.comp hg (.const n)
  have le (n : ℕ) {g : α → ℕ} (hg : Primrec g) : PrimrecPred fun x => n ≤ g x :=
    Primrec.nat_le.comp (.const n) hg
  have mod {g : α → ℕ} (hg : Primrec g) (n : ℕ) : PrimrecPred fun x => g x % 2 = n :=
    Primrec.eq.comp (Primrec.nat_mod.comp hg (.const 2)) (.const n)
  have tile {g : α → ℕ} (hg : Primrec g) : Primrec fun x => tileOfCode (f x) (g x) :=
    (Primrec.list_getD _).comp hf
      (Primrec.nat_div.comp (Primrec.nat_sub.comp hg (.const 28)) (.const 2))
  exact ((eq ha 17).and ((eq hb 18).and (eq hc 8))).or <|
    ((le 28 ha).and <| (mod ha 0).and <| (le 28 hb).and <| (mod hb 1).and <| (eq hc 13).and
      (Primrec.eq.comp (primrec_left.comp (tile ha)) (primrec_right.comp (tile hb))).not).or <|
    ((le 28 ha).and <| (mod ha 1).and <| (le 28 hb).and <| (mod hb 0).and <| (eq hc 15).and
      (Primrec.eq.comp (primrec_bottom.comp (tile ha)) (primrec_top.comp (tile hb))).not).or <|
    ((eq ha 21).and <| (eq hb 18).and <| (le 30 hc).and (mod hc 0)).or <|
    ((eq ha 23).and <| (eq hb 16).and <| (le 31 hc).and (mod hc 1)).or <|
    ((eq ha 25).and <| (eq hb 16).and ((eq hc 12).or (eq hc 13))).or <|
    (eq ha 27).and <| (eq hb 18).and ((eq hc 14).or (eq hc 15))

private theorem primrecPred_cycleCode {α : Type*} [Primcodable α] {f : α → List WangTile}
    {a b c : α → ℕ} (hf : Primrec f) (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    PrimrecPred fun x => CycleCode (f x) (a x) (b x) (c x) := by
  have ha' := primrec_convCode.comp ha
  have hb' := primrec_convCode.comp hb
  have hc' := primrec_convCode.comp hc
  have imp {g h₁ h₂ : α → ℕ} (hg : Primrec g) (h₁' : Primrec h₁) (h₂' : Primrec h₂) :
      PrimrecPred fun x => g x < 3 → h₁ x = h₂ x :=
    ((Primrec.nat_lt.comp hg (.const 3)).not.or (Primrec.eq.comp h₁' h₂')).of_eq fun x => by
      rw [imp_iff_not_or]
  exact (Primrec.eq.comp (primrec_srcCode.comp ha') (primrec_srcCode.comp hb)).and <|
    (Primrec.eq.comp (primrec_srcCode.comp ha) (primrec_srcCode.comp hc)).and <|
    (Primrec.eq.comp (primrec_srcCode.comp hb') (primrec_srcCode.comp hc')).and <|
    (imp ha hc hb).and <| (imp hb hc ha).and <| (imp hc hb ha').and <|
    ((primrecPred_ruleCode hf ha hb hc).or <| (primrecPred_ruleCode hf hb hc' ha').or <|
      (primrecPred_ruleCode hf hc' ha hb').or <| (primrecPred_ruleCode hf ha' hc hb).or <|
      (primrecPred_ruleCode hf hc hb' ha).or (primrecPred_ruleCode hf hb' ha' hc')).not

private theorem primrec_tilingTable : Primrec tilingTable := by
  have hn : Primrec fun L : List WangTile => 2 * L.length + 28 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) Primrec.list_length) (.const 28)
  have hatoms : Primrec fun L : List WangTile => List.range (2 * L.length + 28) :=
    Primrec.list_range.comp hn
  have htriples : Primrec fun L : List WangTile =>
      (List.range (2 * L.length + 28)).flatMap fun a =>
        (List.range (2 * L.length + 28)).flatMap fun b =>
          (List.range (2 * L.length + 28)).map fun c => (a, b, c) :=
    Primrec.list_flatMap hatoms <| Primrec.list_flatMap (hatoms.comp .fst) <|
      Primrec.list_map (hatoms.comp (Primrec.fst.comp .fst))
        ((Primrec.snd.comp (Primrec.fst.comp .fst)).pair
          ((Primrec.snd.comp .fst).pair .snd)).to₂ |>.to₂ |>.to₂
  have hcycle : PrimrecRel fun (q : List WangTile × ℕ × ℕ × ℕ) (x : ℕ × ℕ × ℕ) =>
      CycleCode q.1 x.1 x.2.1 x.2.2 :=
    primrecPred_cycleCode (Primrec.fst.comp .fst) (Primrec.fst.comp .snd)
      (Primrec.fst.comp (Primrec.snd.comp .snd)) (Primrec.snd.comp (Primrec.snd.comp .snd))
  have hcycles := Primrec.listFilterMap htriples (Primrec.option_guard hcycle .snd).to₂
  exact (Primrec.of_equiv_symm.comp (hn.pair ((Primrec.list_map hatoms
    (primrec_convCode.comp .snd).to₂).pair ((Primrec.const [0, 1, 2]).pair hcycles)))).of_eq
    fun L => congrArg (AtomTable.mk _ _ _) (congrFun List.filterMap_eq_filter _)

private theorem primrec_freshTile : Primrec freshTile := by
  have hc : Primrec fun τ : List WangTile =>
      τ.foldr (fun t c => max (max (max t.top t.bottom) (max t.left t.right) + 1) c) 0 :=
    Primrec.list_foldr .id (.const 0) <| Primrec.nat_max.comp
      (Primrec.succ.comp (Primrec.nat_max.comp
        (Primrec.nat_max.comp (primrec_top.comp (Primrec.fst.comp .snd))
          (primrec_bottom.comp (Primrec.fst.comp .snd)))
        (Primrec.nat_max.comp (primrec_left.comp (Primrec.fst.comp .snd))
          (primrec_right.comp (Primrec.fst.comp .snd)))))
      (Primrec.snd.comp .snd) |>.to₂
  exact primrec_mk hc hc hc hc

/-- The reduction is computable: it sends a list of tiles to the table of `RA(τ⁺)`, where `τ⁺` is
the list with a fresh special tile in front. It is in fact primitive recursive. -/
theorem computable_tilingTable_cons_freshTile :
    Computable fun τ : List WangTile => tilingTable (freshTile τ :: τ) :=
  (primrec_tilingTable.comp (Primrec.list_cons.comp primrec_freshTile .id)).to_comp

/-- Every tile of `τ` is at the origin of a tiling of the plane by `τ` if and only if the table
of `RA(τ⁺)` presents an atom structure whose complex algebra is representable, where `τ⁺` is `τ`
with a fresh special tile in front: the correctness of the reduction of [HirschHodkinson2001].
From left to right it is Theorem 4 with Lemma 7 and Theorem 1, and from right to left Theorems 1
and 3. Theorem 4 uses that the special tile matches itself; that its colour is on no other tile
makes the two tiling problems, for `τ` and for `τ⁺`, agree. -/
theorem everyTileOccurs_iff_isRepresentable (τ : List WangTile) :
    EveryTileOccurs τ ↔ (tilingTable (freshTile τ :: τ)).IsRepresentable := by
  rw [isRepresentable_tilingTable_iff, ← everyTileOccurs_cons_freshTile_iff,
    everyTileOccurs_iff_everyIndexOccurs]
  exact ⟨hasWinningStrategy_tilingFrame (Nat.succ_pos _) rfl rfl,
    everyIndexOccurs_of_hasWinningStrategy⟩

/-- The tiling problem of [HirschHodkinson2001], Section 3, whether every tile of a finite list is
at the origin of a tiling of the plane by the list, many-one reduces to the representation problem
for finite relation algebras given by tables. This is the reduction of the source; that either
problem is undecidable is not stated here. -/
theorem everyTileOccurs_manyOneReducible_isRepresentable :
    EveryTileOccurs ≤₀ AtomTable.IsRepresentable :=
  ⟨_, computable_tilingTable_cons_freshTile, everyTileOccurs_iff_isRepresentable⟩

end Cslib.RelationAlgebra
