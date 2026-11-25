/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Gather
import Mathlib.Tactic.Ring

/-!
# Writing back

The writing passes of a move at level `j` of the Hennie–Stearns machine: the list gathered from
the side of the move is spread over the center and the zones of that side up to `j`
(`runFrom_writeS`), and then the other list over the other side (`runFrom_writeD`), as `move`
lays them out.
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

variable {k : ℕ} {Symbol State : Type} {input : List (HSym k Symbol)}
  (tm : MultiTapeTM k Symbol State) (q : State) (mv : Fin k → SignType) (i : Fin k)
  (p : Fin (input.length + 2)) (out : List (HSym k Symbol))

/-! ### Tapes rewritten up to a cell -/

/-- Work tape `0` rewritten from `A` to `A'` below cell `t`. -/
def mixA (A A' : ℤ → Option (HSym k Symbol)) (t : ℕ) : ℤ → Option (HSym k Symbol) :=
  fun z => if z < t then A' z else A z

lemma mixA_self (A A' : ℤ → Option (HSym k Symbol)) (t : ℕ) : mixA A A' t t = A t := by
  simp [mixA]

lemma update_mixA (A A' : ℤ → Option (HSym k Symbol)) (t : ℕ) :
    Function.update (mixA A A' t) (t : ℤ) (A' t) = mixA A A' (t + 1) := by
  funext z
  by_cases hz : z = t
  · subst hz; simp [mixA]
  · rw [Function.update_of_ne hz]
    simp only [mixA, Nat.cast_add, Nat.cast_one]
    congr 1
    apply propext
    omega

lemma update_mixA_of_eq {A A' : ℤ → Option (HSym k Symbol)} {t : ℕ} {v : Option (HSym k Symbol)}
    (h : A' t = v) : Function.update (mixA A A' t) (t : ℤ) v = mixA A A' (t + 1) := by
  rw [← h, update_mixA]

lemma mixA_succ_of_eq {A A' : ℤ → Option (HSym k Symbol)} {t : ℕ} (h : A t = A' t) :
    mixA A A' (t + 1) = mixA A A' t := by
  rw [← update_mixA, ← h, ← mixA_self A A' t, Function.update_eq_self]

lemma mixA_zero {A A' : ℤ → Option (HSym k Symbol)} (h : ∀ z < 0, A' z = A z) :
    mixA A A' 0 = A := by
  funext z
  simp only [mixA, Nat.cast_zero]
  split_ifs with hz
  · exact h z hz
  · rfl

lemma mixA_eq_of_ge {A A' : ℤ → Option (HSym k Symbol)} {t : ℕ} (h : ∀ z : ℤ, t ≤ z → A z = A' z) :
    mixA A A' t = A' := by
  funext z
  simp only [mixA]
  split_ifs with hz
  · rfl
  · exact h z (by omega)

/-- Cell `p ≥ 1` of work tape `1` holding the lists `src` and `dst`, with the first `cs` cells of
`src` and the first `cd` cells of `dst` cleared. -/
def bCellX (cs cd : ℕ) (src dst : List (Option Symbol)) (p : ℕ) : BCell Symbol :=
  ⟨if p ≤ cs then none else src[p - 1]?, if p ≤ cd then none else dst[p - 1]?, false, false,
    false⟩

/-- Work tape `1` holding the lists `src` and `dst`, partly cleared. -/
def encBX (cs cd : ℕ) (src dst : List (Option Symbol)) : ℤ → Option (HSym k Symbol) :=
  fun z => if z = 0 then some (.inr (.inr homeCell))
    else if 0 < z then bWrite (bCellX cs cd src dst z.toNat) else none

lemma encBX_zero_zero (src dst : List (Option Symbol)) :
    encBX (k := k) 0 0 src dst = encB src dst := by
  funext z
  simp only [encBX, encB, bCellX, bCell]
  split_ifs <;> first | rfl | omega

lemma bCellX_length_s (src dst : List (Option Symbol)) {p : ℕ} (hp : 1 ≤ p) :
    bCellX src.length 0 src dst p = bCell [] dst p := by
  simp only [bCellX, bCell, List.getElem?_nil, show ¬ p ≤ 0 by omega, ↓reduceIte, BCell.mk.injEq,
    and_true]
  split_ifs
  · rfl
  · exact List.getElem?_eq_none (by omega)

lemma encBX_length_s (src dst : List (Option Symbol)) :
    encBX (k := k) src.length 0 src dst = encB [] dst := by
  funext z
  simp only [encBX, encB]
  split_ifs with h₀ h₁ <;> try rfl
  rw [bCellX_length_s _ _ (by omega)]

lemma bCellX_length_d (dst : List (Option Symbol)) {p : ℕ} (hp : 1 ≤ p) :
    bCellX 0 dst.length [] dst p = bCell (Symbol := Symbol) [] [] p := by
  simp only [bCellX, bCell, List.getElem?_nil, show ¬ p ≤ 0 by omega, ↓reduceIte, BCell.mk.injEq,
    true_and, and_true]
  split_ifs
  · rfl
  · exact List.getElem?_eq_none (by omega)

lemma encBX_length_d (dst : List (Option Symbol)) :
    encBX (k := k) 0 dst.length [] dst = encB [] [] := by
  funext z
  simp only [encBX, encB]
  split_ifs with h₀ h₁ <;> try rfl
  rw [bCellX_length_d _ (by omega)]

lemma readB_encBX_pos (cs cd : ℕ) (src dst : List (Option Symbol)) {z : ℤ} (hz : 0 < z) :
    readB (encBX (k := k) cs cd src dst z) = bCellX cs cd src dst z.toNat := by
  simp [encBX, show z ≠ 0 by omega, hz, readB_bWrite]

lemma encBX_pop_s (cs cd : ℕ) (src dst : List (Option Symbol)) :
    Function.update (encBX (k := k) cs cd src dst) ((cs : ℤ) + 1)
        (bWrite { bCellX cs cd src dst (cs + 1) with s := none }) =
      encBX (cs + 1) cd src dst := by
  funext z
  by_cases hz : z = (cs : ℤ) + 1
  · subst hz
    rw [Function.update_self]
    simp only [encBX]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    simp [bCellX, show ((cs : ℤ) + 1).toNat = cs + 1 by omega]
  · rw [Function.update_of_ne hz]
    simp only [encBX]
    split_ifs with h₀ h₁ <;> try rfl
    simp only [bCellX]
    congr 3
    apply propext
    omega

lemma encBX_pop_d (cs cd : ℕ) (src dst : List (Option Symbol)) :
    Function.update (encBX (k := k) cs cd src dst) ((cd : ℤ) + 1)
        (bWrite { bCellX cs cd src dst (cd + 1) with d := none }) =
      encBX cs (cd + 1) src dst := by
  funext z
  by_cases hz : z = (cd : ℤ) + 1
  · subst hz
    rw [Function.update_self]
    simp only [encBX]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    simp [bCellX, show ((cd : ℤ) + 1).toNat = cd + 1 by omega]
  · rw [Function.update_of_ne hz]
    simp only [encBX]
    split_ifs with h₀ h₁ <;> try rfl
    simp only [bCellX]
    congr 3
    apply propext
    omega

/-! ### Rewriting cells -/

/-- The track `Y'` on side `s` and at the center, and `Y` on the other side. -/
def ZTrack.withSide (Y Y' : ZTrack Symbol) (s : Side) : ZTrack Symbol :=
  { center := Y'.center, zone := fun s' => if s' = s then Y'.zone s else Y.zone s' }

@[simp] lemma ZTrack.withSide_zone_self (Y Y' : ZTrack Symbol) (s : Side) :
    (Y.withSide Y' s).zone s = Y'.zone s := by
  simp [ZTrack.withSide]

@[simp] lemma ZTrack.withSide_zone_other (Y Y' : ZTrack Symbol) (s : Side) :
    (Y.withSide Y' s).zone s.other = Y.zone s.other := by
  simp [ZTrack.withSide]

lemma zoneCell_update (Z : Fin k → ZTrack Symbol) (tg : Option ℕ) (n : ℕ) (i : Fin k) (s : Side)
    (Y : ZTrack Symbol) (hY : Y.zone s.other = (Z i).zone s.other) :
    zoneCell (Function.update Z i Y) tg n =
      (zoneCell Z tg n).setPart s i ((Y.zone s (lvl n))[off n]?) := by
  cases s <;>
  · simp only [zoneCell, ACell.setPart, ACell.mk.injEq, true_and]
    refine ⟨funext fun i' => ?_, funext fun i' => ?_⟩ <;>
    · by_cases h : i' = i
      · subst h; simp_all [Side.other]
      · simp [Function.update_of_ne h]

lemma centerCell_update (Z : Fin k → ZTrack Symbol) (i : Fin k) (Y : ZTrack Symbol) :
    centerCell (Function.update Z i Y) =
      { centerCell Z with r := Function.update (centerCell Z).r i (some Y.center) } := by
  simp only [centerCell, ACell.mk.injEq, true_and, and_true]
  funext i'
  by_cases h : i' = i
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- Work tape `0` beyond zone `j` does not depend on the zones up to `j`, nor on a mark in
them. -/
lemma encA_eq_of_ge {Z Z' : Fin k → ZTrack Symbol} {J j : ℕ} {tg tg' : Option ℕ}
    (hZ : ∀ i s m, j < m → (Z' i).zone s m = (Z i).zone s m)
    (htg : ∀ m, tg = some m → m ≤ j) (htg' : ∀ m, tg' = some m → m ≤ j)
    (z : ℤ) (hz : (zs (j + 1) : ℤ) ≤ z) : encA Z J tg z = encA Z' J tg' z := by
  have h1 := one_le_zs (j + 1)
  have hn : 1 ≤ z.toNat := by omega
  have hl : j < lvl z.toNat := by
    by_contra h
    have := lt_zs_of_lvl_lt hn (show lvl z.toNat < j + 1 by omega)
    omega
  simp only [encA, show 0 ≤ z by omega, ↓reduceIte, aCell, show z.toNat ≠ 0 by omega]
  split_ifs
  · congr 2
    simp only [zoneCell, ACell.mk.injEq, true_and]
    refine ⟨?_, funext fun i => by rw [hZ i _ _ hl], funext fun i => by rw [hZ i _ _ hl]⟩
    rw [decide_eq_decide]
    constructor
    · rintro ⟨h, -⟩; have := htg _ h; omega
    · rintro ⟨h, -⟩; have := htg' _ h; omega
  · rfl

/-! ### The next item to write -/

/-- What a pass reading the zones `L` of one side, with `c` at the center, takes from cell
`n`. -/
def item {α : Type*} (c : List α) (L : ℕ → List α) (n : ℕ) : List α :=
  if n = 0 then c else (L (lvl n))[off n]?.toList

/-- In a pass spreading the list `U` over zones half full below level `j`, the next item of `U`
is the one cell `t` holds, and exists exactly when the cell is in the first half of its zone, or
the list is not used up in zone `j`. -/
lemma item_next {α : Type*} (c : List α) (L : ℕ → List α) {j : ℕ}
    (hlt : ∀ m < j, (L m).length = 2 ^ m) (hj : (L j).length ≤ 2 ^ (j + 1)) {t : ℕ}
    (ht0 : 1 ≤ t) (ht : t < zs (j + 1)) :
    (if zs j ≤ t then ((c ++ (List.range (j + 1)).flatMap L)[
        ((List.range t).flatMap (item c L)).length]?).isSome
      else decide (off t < 2 ^ lvl t)) = ((L (lvl t))[off t]?).isSome ∧
      ∀ x, (L (lvl t))[off t]? = some x → (c ++ (List.range (j + 1)).flatMap L)[
        ((List.range t).flatMap (item c L)).length]? = some x := by
  set U := c ++ (List.range (j + 1)).flatMap L
  set P := (List.range t).flatMap (item c L)
  have hl := lvl_lt_of_lt_zs ht0 ht
  have hU : U = P ++ (List.range (zs (j + 1) - t)).flatMap fun u => item c L (t + u) := by
    have := flatMap_cells L c j fun m hm => by
      rcases Nat.lt_or_ge m j with h | h
      · rw [hlt m h, pow_succ]; omega
      · rw [show m = j by omega]; exact hj
    simp only [U, P, ← this]
    conv_lhs => rw [show zs (j + 1) = t + (zs (j + 1) - t) by omega, List.range_add,
      List.flatMap_append, List.flatMap_map]
    rfl
  have hR : ((List.range (zs (j + 1) - t)).flatMap fun u => item c L (t + u)) =
      item c L t ++ (List.range (zs (j + 1) - (t + 1))).flatMap fun u => item c L (t + 1 + u) := by
    rw [show zs (j + 1) - t = 1 + (zs (j + 1) - (t + 1)) by omega, List.range_add,
      List.flatMap_append, List.flatMap_map]
    simp [Nat.add_comm 1, Nat.add_assoc]
  have hget : U[P.length]? = (item c L t ++ (List.range (zs (j + 1) - (t + 1))).flatMap
      fun u => item c L (t + 1 + u))[0]? := by
    rw [hU, hR, List.getElem?_append_right le_rfl, Nat.sub_self]
  have hit : item c L t = ((L (lvl t))[off t]?).toList := by simp [item, show t ≠ 0 by omega]
  rw [hget, hit]
  rcases hv : (L (lvl t))[off t]? with _ | x
  · simp only [Option.toList_none, List.nil_append, Option.isSome_none, reduceCtorEq,
      IsEmpty.forall_iff, implies_true, and_true]
    have hlen : (L (lvl t)).length ≤ off t := List.getElem?_eq_none_iff.1 hv
    split_ifs with hz
    · have hlj : lvl t = j := lvl_eq hz ht
      rw [List.flatMap_eq_nil_iff.2 fun u hu => ?_]
      · simp
      have hu := List.mem_range.1 hu
      have h1 : zs j ≤ t + 1 + u := by omega
      have h2 : t + 1 + u < zs (j + 1) := by omega
      simp only [item, show t + 1 + u ≠ 0 by omega, ↓reduceIte, lvl_eq h1 h2,
        Option.toList_eq_nil_iff]
      rw [off_eq h1 h2, List.getElem?_eq_none]
      rw [hlj, off_eq hz ht] at hlen
      omega
    · have hlj : lvl t < j := by
        by_contra h
        have := zs_mono (show j ≤ lvl t by omega)
        have := (zs_lvl_le ht0).1
        omega
      rw [hlt _ hlj] at hlen
      simp only [decide_eq_false_iff_not, not_lt]
      exact hlen
  · simp only [Option.toList_some, List.cons_append, List.getElem?_cons_zero, Option.isSome_some,
      Option.some.injEq, forall_eq', and_true]
    split_ifs with hz
    · rfl
    · have hlj : lvl t < j := by
        by_contra h
        have := zs_mono (show j ≤ lvl t by omega)
        have := (zs_lvl_le ht0).1
        omega
      have := List.getElem?_eq_some_iff.1 hv
      obtain ⟨hlt', -⟩ := this
      rw [hlt _ hlj] at hlt'
      simpa using hlt'

/-! ### The writing passes -/

lemma bCellX_s_next (cs cd : ℕ) (src dst : List (Option Symbol)) :
    (bCellX cs cd src dst (cs + 1)).s = src[cs]? := by
  simp [bCellX]

lemma bCellX_d_next (cs cd : ℕ) (src dst : List (Option Symbol)) :
    (bCellX cs cd src dst (cd + 1)).d = dst[cd]? := by
  simp [bCellX]

lemma encA_neg (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ) {z : ℤ} (hz : z < 0) :
    encA Z J tg z = none := by
  simp [encA, show ¬ 0 ≤ z by omega]

/-- The zones up to the level of a move to `s`, as the move lays out the gathered list. -/
lemma move_layout (Y : ZTrack Symbol) {J : ℕ} (hV : Y.Valid J) (s : Side) :
    [(Y.move J s).center] ++ (List.range (Y.trig J s + 1)).flatMap ((Y.move J s).zone s) =
      Y.zone s (Y.trig J s) := by
  have hlen := ZTrack.length_zone_trig hV s
  rw [List.flatMap_congr fun m hm =>
      ZTrack.zone_move_self_of_le (by have := List.mem_range.1 hm; omega),
    ZTrack.flatMap_fill _ _ (by simp; omega)]
  rcases h : Y.zone s (Y.trig J s) with _ | ⟨a, l⟩
  · exact absurd h (ZTrack.zone_trig_ne_nil hV s)
  · simp [ZTrack.move, h]

/-- The other zones up to the level of a move to `s`, as the move lays out the gathered list. -/
lemma move_layout_other (Y : ZTrack Symbol) {J : ℕ} (hV : Y.Valid J) (s : Side) :
    (List.range (Y.trig J s + 1)).flatMap ((Y.move J s).zone s.other) =
      Y.center :: (List.range (Y.trig J s + 1)).flatMap (Y.zone s.other) := by
  have hlen := ZTrack.length_dst hV s
  rw [List.flatMap_congr fun m hm =>
      ZTrack.zone_move_other_of_le (by have := List.mem_range.1 hm; omega),
    ZTrack.flatMap_fill _ _ (by rw [hlen]; omega)]

lemma length_move_zone_le (Y : ZTrack Symbol) {J : ℕ} (hV : Y.Valid J) (s s' : Side) :
    ((Y.move J s).zone s' (Y.trig J s)).length ≤ 2 ^ (Y.trig J s + 1) := by
  have := (hV.move s).length s' (Y.trig J s)
  rw [pow_succ] at this ⊢
  omega

/-- **Writing the side of the move.** From the center, the machine spreads the list gathered from
the side of the move of track `i` over the center and the zones of that side up to the level `j`
of the move, as `move` lays it out, and stops at the end of zone `j`. -/
lemma runFrom_writeS (Z : Fin k → ZTrack Symbol) {J : ℕ} (hV : (Z i).Valid J)
    (hj : (Z i).trig J (srcSide mv i) < J) (D : List (Option Symbol)) :
    (hennieStearns tm).runFrom
        (C q mv i p out (.writeS false) (encA Z J (some ((Z i).trig J (srcSide mv i))))
          (encB ((Z i).zone (srcSide mv i) ((Z i).trig J (srcSide mv i))) D) 0 1)
        (zs ((Z i).trig J (srcSide mv i) + 1) + 1) =
      C q mv i p out (.back .writeD)
        (encA (Function.update Z i
          ((Z i).withSide ((Z i).move J (srcSide mv i)) (srcSide mv i))) J
          (some ((Z i).trig J (srcSide mv i))))
        (encB [] D) (zs ((Z i).trig J (srcSide mv i) + 1) - 1)
        (((Z i).zone (srcSide mv i) ((Z i).trig J (srcSide mv i))).length + 1) := by
  set s := srcSide mv i
  set j := (Z i).trig J s with hjdef
  set M := (Z i).move J s
  set Z₁ := Function.update Z i ((Z i).withSide M s)
  set S := (Z i).zone s j
  set A := encA Z J (some j)
  set A' := encA Z₁ J (some j)
  let Pt : ℕ → List (Option Symbol) := fun t => (List.range t).flatMap (item [M.center] (M.zone s))
  have hPt : ∀ t, Pt (t + 1) = Pt t ++ item [M.center] (M.zone s) t := fun t => by
    simp [Pt, List.range_succ, List.flatMap_append]
  have hU : [M.center] ++ (List.range (j + 1)).flatMap (M.zone s) = S := move_layout _ hV s
  have hlt : ∀ m < j, (M.zone s m).length = 2 ^ m := fun m hm =>
    ZTrack.length_zone_move_of_lt hV s hm
  have hjl : (M.zone s j).length ≤ 2 ^ (j + 1) := length_move_zone_le _ hV s s
  have hfin : Pt (zs (j + 1)) = S := by
    rw [← hU]
    exact flatMap_cells _ _ j fun m hm => by
      rcases Nat.lt_or_ge m j with h | h
      · rw [hlt m h, pow_succ]; omega
      · rw [show m = j by omega]; exact hjl
  have hY : ((Z i).withSide M s).zone s.other = (Z i).zone s.other := by simp
  have hrun := runFrom_of_step tm (G := fun t => C q mv i p out
    (.writeS (decide (zs j < t))) (mixA A A' t) (encBX (Pt t).length 0 S D) t ((Pt t).length + 1))
    (W := zs (j + 1)) fun t ht => by
      rw [step_op, mixA_self, readA_encA_nat, readB_encBX_pos _ _ _ _ (by omega),
        show (((Pt t).length : ℤ) + 1).toNat = (Pt t).length + 1 by omega]
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · have hS : S[0]? = some M.center := by rw [← hU]; rfl
        have hP1 : Pt (0 + 1) = [M.center] := by simp [hPt, item, Pt]
        simp only [aCell_zero, opTr, centerCell_center, ↓reduceIte, act_apply, Option.elim_some,
          bCellX_s_next, show (Pt 0).length = 0 from rfl, hS, hP1]
        rw [update_mixA_of_eq ?_]
        · erw [encBX_pop_s]
          have h1 : decide (zs j < 0 + 1) = decide (zs j < 0) := by
            have := one_le_zs j; simp; omega
          rw [h1]
          congr 1
        · simp [A', Z₁, encA, aCell, centerCell_update, ZTrack.withSide]
      · have hl : lvl t < J := by have := lvl_lt_of_lt_zs ht0 ht; omega
        rw [aCell_of_lt ht0 hl]
        simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte, gather_no_stop Z t ht0 ht,
          trig_zoneCell Z t ht0, bCellX_s_next]
        have hseen : (decide (zs j < t) || decide (t = zs j)) = decide (zs j < t + 1) := by
          by_cases h : zs j < t <;> by_cases h' : t = zs j <;> simp [h, h'] <;> omega
        rw [hseen]
        obtain ⟨hc, hx⟩ := item_next [M.center] (M.zone s) hlt hjl ht0 ht
        rw [hU] at hc hx
        have hcond : (if decide (zs j < t + 1) = true then S[(Pt t).length]?.isSome
            else (zoneCell Z (some j) t).inner) = (M.zone s (lvl t))[off t]?.isSome := by
          rw [← hc]
          by_cases h : zs j ≤ t
          · simp only [h, ↓reduceIte, show zs j < t + 1 by omega, decide_true]
            rfl
          · simp [h, show ¬ zs j < t + 1 by omega, zoneCell]
        have hA : ∀ v, (M.zone s (lvl t))[off t]? = v →
            A' t = some (.inr (.inl ((zoneCell Z (some j) t).setPart s i v))) := by
          rintro v rfl
          simp only [A', encA_natCast, aCell_of_lt ht0 hl, Option.map_some, Z₁,
            zoneCell_update Z _ t i s _ hY, ZTrack.withSide_zone_self]
        rw [hcond]
        rcases hv : (M.zone s (lvl t))[off t]? with _ | x
        · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, act_apply,
            Option.elim_some, Option.elim_none]
          rw [update_mixA_of_eq (hA none hv)]
          have : Pt (t + 1) = Pt t := by
            rw [hPt]; simp [item, show t ≠ 0 by omega, hv]
          rw [this]
          congr 1
        · have hsx : S[(Pt t).length]? = some x := hx x hv
          simp only [Option.isSome_some, ↓reduceIte, act_apply, Option.elim_some, hsx]
          rw [update_mixA_of_eq (hA _ hv)]
          erw [encBX_pop_s]
          have : Pt (t + 1) = Pt t ++ [x] := by
            rw [hPt]; simp [item, show t ≠ 0 by omega, hv]
          rw [this]
          congr 1 <;> simp
  have h0 : mixA A A' 0 = A := mixA_zero fun z hz => by simp only [A, A', encA_neg _ _ _ hz]
  simp only [h0, show (Pt 0).length = 0 from rfl, encBX_zero_zero, Nat.cast_zero, zero_add,
    Nat.not_lt_zero, decide_false] at hrun
  have hend : ∀ z : ℤ, (zs (j + 1) : ℤ) ≤ z → A z = A' z := fun z hz =>
    encA_eq_of_ge (fun i' s' m hm => by
      by_cases h : i' = i
      · subst h
        simp only [Z₁, Function.update_self, ZTrack.withSide]
        split_ifs with hs
        · subst hs; exact ZTrack.zone_move_of_lt hm
        · rfl
      · simp [Z₁, Function.update_of_ne h])
      (fun m hm => by cases hm; rfl) (fun m hm => by cases hm; rfl) z hz
  have hseen : decide (zs j < zs (j + 1)) = true := by simp [zs_strictMono (Nat.lt_succ_self j)]
  rw [runFrom_add, hrun, runFrom_one, step_op, mixA_self, readA_encA_nat, hseen]
  rcases Nat.lt_or_ge (j + 1) J with hJ | hJ
  · rw [aCell_of_lt (one_le_zs _) (by rw [lvl_zs]; exact hJ)]
    simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte,
      show (zoneCell Z (some j) (zs (j + 1))).start = true by simp [zoneCell, off_zs],
      Bool.true_and, act_apply, Option.elim_none]
    rw [hfin, encBX_length_s, mixA_eq_of_ge hend]
    congr 1
  · rw [aCell_of_le (one_le_zs _) (by rw [lvl_zs]; exact hJ)]
    simp only [opTr, act_apply, Option.elim_none]
    rw [hfin, encBX_length_s, mixA_eq_of_ge hend]
    congr 1

/-- **Writing the other side.** From the center, the machine spreads the list gathered from the
other side of track `i`, with the center, over the zones of that side up to the level `j` of the
move, as `move` lays it out, clears the mark of zone `j`, and stops at the end of zone `j`. -/
lemma runFrom_writeD (Z : Fin k → ZTrack Symbol) {J : ℕ} (hV : (Z i).Valid J)
    (hj : (Z i).trig J (srcSide mv i) < J) :
    (hennieStearns tm).runFrom
        (C q mv i p out (.writeD false)
          (encA (Function.update Z i
            ((Z i).withSide ((Z i).move J (srcSide mv i)) (srcSide mv i))) J
            (some ((Z i).trig J (srcSide mv i))))
          (encB [] ((Z i).center :: (List.range ((Z i).trig J (srcSide mv i) + 1)).flatMap
            ((Z i).zone (srcSide mv i).other))) 0 1)
        (zs ((Z i).trig J (srcSide mv i) + 1) + 1) =
      C q mv i p out (.back .done)
        (encA (Function.update Z i ((Z i).move J (srcSide mv i))) J none)
        (encB [] []) (zs ((Z i).trig J (srcSide mv i) + 1) - 1)
        (((Z i).center :: (List.range ((Z i).trig J (srcSide mv i) + 1)).flatMap
          ((Z i).zone (srcSide mv i).other)).length + 1) := by
  set s := srcSide mv i
  set o := s.other
  set j := (Z i).trig J s with hjdef
  set M := (Z i).move J s
  set Z₁ := Function.update Z i ((Z i).withSide M s)
  set Z₂ := Function.update Z i M
  set D := (Z i).center :: (List.range (j + 1)).flatMap ((Z i).zone o)
  set A := encA Z₁ J (some j)
  set A' := encA Z₂ J none
  let Qt : ℕ → List (Option Symbol) := fun t => (List.range t).flatMap (item [] (M.zone o))
  have hQt : ∀ t, Qt (t + 1) = Qt t ++ item [] (M.zone o) t := fun t => by
    simp [Qt, List.range_succ, List.flatMap_append]
  have hU : [] ++ (List.range (j + 1)).flatMap (M.zone o) = D := move_layout_other _ hV s
  have hlt : ∀ m < j, (M.zone o m).length = 2 ^ m := fun m hm =>
    ZTrack.length_zone_move_of_lt hV o hm
  have hjl : (M.zone o j).length ≤ 2 ^ (j + 1) := length_move_zone_le _ hV s o
  have hfin : Qt (zs (j + 1)) = D := by
    rw [← hU]
    exact flatMap_cells _ _ j fun m hm => by
      rcases Nat.lt_or_ge m j with h | h
      · rw [hlt m h, pow_succ]; omega
      · rw [show m = j by omega]; exact hjl
  have hZ₂ : Z₂ = Function.update Z₁ i M := by simp [Z₂, Z₁]
  have hY : M.zone o.other = (Z₁ i).zone o.other := by simp [o, Z₁]
  have hrun := runFrom_of_step tm (G := fun t => C q mv i p out
    (.writeD (decide (zs j < t))) (mixA A A' t) (encBX 0 (Qt t).length [] D) t ((Qt t).length + 1))
    (W := zs (j + 1)) fun t ht => by
      rw [step_op, mixA_self, readA_encA_nat, readB_encBX_pos _ _ _ _ (by omega),
        show (((Qt t).length : ℤ) + 1).toNat = (Qt t).length + 1 by omega]
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · have hQ1 : Qt (0 + 1) = Qt 0 := by simp [hQt, item]
        simp only [aCell_zero, opTr, centerCell_center, ↓reduceIte, act_apply, Option.elim_none]
        rw [hQ1, mixA_succ_of_eq]
        · have h1 : decide (zs j < 0 + 1) = decide (zs j < 0) := by
            have := one_le_zs j; simp; omega
          rw [h1]
          congr 1
        · simp [A, A', encA, aCell, Z₁, Z₂, centerCell_update, ZTrack.withSide]
      · have hl : lvl t < J := by have := lvl_lt_of_lt_zs ht0 ht; omega
        rw [aCell_of_lt ht0 hl]
        simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte,
          gather_no_stop Z₁ t ht0 ht, trig_zoneCell Z₁ t ht0, bCellX_d_next]
        have hseen : (decide (zs j < t) || decide (t = zs j)) = decide (zs j < t + 1) := by
          by_cases h : zs j < t <;> by_cases h' : t = zs j <;> simp [h, h'] <;> omega
        rw [hseen]
        obtain ⟨hc, hx⟩ := item_next [] (M.zone o) hlt hjl ht0 ht
        rw [hU] at hc hx
        have hcond : (if decide (zs j < t + 1) = true then D[(Qt t).length]?.isSome
            else (zoneCell Z₁ (some j) t).inner) = (M.zone o (lvl t))[off t]?.isSome := by
          rw [← hc]
          by_cases h : zs j ≤ t
          · simp only [h, ↓reduceIte, show zs j < t + 1 by omega, decide_true]
            rfl
          · simp [h, show ¬ zs j < t + 1 by omega, zoneCell]
        have hA : ∀ v, (M.zone o (lvl t))[off t]? = v →
            A' t = some (.inr (.inl ({ zoneCell Z₁ (some j) t with trig := false }.setPart o i
              v))) := by
          rintro v rfl
          have : { zoneCell Z₁ (some j) t with trig := false } = zoneCell Z₁ none t := by
            simp [zoneCell]
          rw [this]
          simp only [A', encA_natCast, aCell_of_lt ht0 hl, Option.map_some, hZ₂,
            zoneCell_update Z₁ _ t i o _ hY]
        rw [hcond]
        rcases hv : (M.zone o (lvl t))[off t]? with _ | x
        · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, act_apply,
            Option.elim_some, Option.elim_none]
          erw [update_mixA_of_eq (hA none hv)]
          have : Qt (t + 1) = Qt t := by
            rw [hQt]; simp [item, show t ≠ 0 by omega, hv]
          rw [this]
          congr 1
        · have hsx : D[(Qt t).length]? = some x := hx x hv
          simp only [Option.isSome_some, ↓reduceIte, act_apply, Option.elim_some, hsx]
          erw [update_mixA_of_eq (hA _ hv)]
          erw [encBX_pop_d]
          have : Qt (t + 1) = Qt t ++ [x] := by
            rw [hQt]; simp [item, show t ≠ 0 by omega, hv]
          rw [this]
          congr 1 <;> simp
  have h0 : mixA A A' 0 = A := mixA_zero fun z hz => by simp only [A, A', encA_neg _ _ _ hz]
  simp only [h0, show (Qt 0).length = 0 from rfl, encBX_zero_zero, Nat.cast_zero, zero_add,
    Nat.not_lt_zero, decide_false] at hrun
  have hend : ∀ z : ℤ, (zs (j + 1) : ℤ) ≤ z → A z = A' z := fun z hz =>
    encA_eq_of_ge (fun i' s' m hm => by
      by_cases h : i' = i
      · subst h
        simp only [Z₁, Z₂, Function.update_self, ZTrack.withSide]
        split_ifs with hs
        · rw [hs]
        · exact ZTrack.zone_move_of_lt hm
      · simp [Z₁, Z₂, Function.update_of_ne h])
      (fun m hm => by cases hm; rfl) (fun m hm => by cases hm) z hz
  have hseen : decide (zs j < zs (j + 1)) = true := by simp [zs_strictMono (Nat.lt_succ_self j)]
  rw [runFrom_add, hrun, runFrom_one, step_op, mixA_self, readA_encA_nat, hseen]
  rcases Nat.lt_or_ge (j + 1) J with hJ | hJ
  · rw [aCell_of_lt (one_le_zs _) (by rw [lvl_zs]; exact hJ)]
    simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte,
      show (zoneCell Z₁ (some j) (zs (j + 1))).start = true by simp [zoneCell, off_zs],
      Bool.true_and, act_apply, Option.elim_none]
    rw [hfin, encBX_length_d, mixA_eq_of_ge hend]
    congr 1
  · rw [aCell_of_le (one_le_zs _) (by rw [lvl_zs]; exact hJ)]
    simp only [opTr, act_apply, Option.elim_none]
    rw [hfin, encBX_length_d, mixA_eq_of_ge hend]
    congr 1

end Turing.MultiTapeTM.HennieStearns
