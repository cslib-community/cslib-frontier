/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Run
import Mathlib.Tactic.Ring

/-!
# Scanning and walking home

The first phases of a move of the Hennie–Stearns machine: the scan for the first zone holding a
symbol on the side of the move (`runFrom_scan`, or `runFrom_scan_blank` when no created zone
does), and the walks of the two work heads home (`runFrom_back`, `runFrom_backB`).
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

variable {k : ℕ} {Symbol State : Type} {input : List (HSym k Symbol)}
  (tm : MultiTapeTM k Symbol State) (q : State) (mv : Fin k → SignType) (i : Fin k)
  (p : Fin (input.length + 2)) (out : List (HSym k Symbol))

/-- The configuration of the move of track `i` in phase `ph`. -/
abbrev C (ph : Phase) (A B : ℤ → Option (HSym k Symbol)) (pA pB : ℤ) :
    Cfg 2 (HSym k Symbol) (HState k State) input :=
  hcfg (some (.op q mv i ph)) p A B pA pB out

lemma part_zoneCell (Z : Fin k → ZTrack Symbol) (tg : Option ℕ) (n : ℕ) (s : Side) (i : Fin k) :
    (zoneCell Z tg n).part s i = ((Z i).zone s (lvl n))[off n]? := by
  cases s <;> rfl

/-- Marking the first cell of zone `j`. -/
lemma update_encA_trig (Z : Fin k → ZTrack Symbol) {J j : ℕ} (hj : j < J) :
    Function.update (encA Z J none) (zs j : ℤ)
        (some (.inr (.inl { zoneCell Z none (zs j) with trig := true }))) =
      encA Z J (some j) := by
  funext z
  by_cases hz : z = zs j
  · subst hz
    rw [Function.update_self, encA_natCast, aCell_of_lt (one_le_zs j) (by rw [lvl_zs]; exact hj)]
    simp [zoneCell, lvl_zs, off_zs]
  · rw [Function.update_of_ne hz]
    simp only [encA]
    split_ifs with h
    · congr 1
      simp only [aCell]
      split_ifs
      · rfl
      · simp only [zoneCell, Option.some.injEq, ACell.mk.injEq, true_and, and_true]
        simp only [decide_eq_decide]
        constructor
        · rintro ⟨h', -⟩
          cases h'
        · rintro ⟨h', h''⟩
          exfalso
          apply hz
          have := zs_lvl_le (n := z.toNat) (by omega)
          simp only [off] at h''
          rw [← h'] at this h''
          omega
      · rfl
    · rfl

/-- **Scanning.** The move of track `i` to side `s` at level `j < J` finds and marks the first
cell of zone `j`. -/
lemma runFrom_scan (Z : Fin k → ZTrack Symbol) {J : ℕ} (hV : (Z i).Valid J)
    (hj : (Z i).trig J (srcSide mv i) < J) (B : ℤ → Option (HSym k Symbol)) (pB : ℤ) :
    (hennieStearns tm).runFrom (C q mv i p out .scan (encA Z J none) B 0 pB)
        (zs ((Z i).trig J (srcSide mv i)) + 1) =
      C q mv i p out (.back .gatherD) (encA Z J (some ((Z i).trig J (srcSide mv i)))) B
        (zs ((Z i).trig J (srcSide mv i)) - 1) pB := by
  set j := (Z i).trig J (srcSide mv i) with hjdef
  rw [runFrom_add, runFrom_walk tm q mv i .scan p _ _ 0 pB out 1 0 (zs j) fun u hu => by
    simp only [SignType.coe_one, one_mul, zero_add, SignType.coe_zero, zero_mul, add_zero]
    rw [readA_encA_nat]
    rcases Nat.eq_zero_or_pos u with rfl | hu0
    · simp [aCell_zero, opTr, centerCell]
    · have hl := lvl_lt_of_lt_zs hu0 hu
      rw [aCell_of_lt hu0 (by omega)]
      simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte, part_zoneCell,
        ZTrack.zone_of_lt_trig hV hl, List.getElem?_nil, Option.isSome_none]]
  simp only [SignType.coe_one, one_mul, zero_add, SignType.coe_zero, zero_mul, add_zero]
  rw [runFrom_one, step_op, readA_encA_nat, aCell_of_lt (one_le_zs j) (by rw [lvl_zs]; exact hj)]
  have hreal : ((zoneCell Z none (zs j)).part (srcSide mv i) i).isSome = true := by
    rw [part_zoneCell, lvl_zs, off_zs]
    rcases h : (Z i).zone (srcSide mv i) j with _ | ⟨a, l⟩
    · exact absurd h (ZTrack.zone_trig_ne_nil hV _)
    · simp
  simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte, hreal, act_apply,
    Option.elim_some, Option.elim_none]
  rw [← update_encA_trig Z hj]
  congr 1
  simp

/-- **Scanning, no zone found.** If no created zone holds a symbol on the side of the move, the
scan reaches the blank after the zones. -/
lemma runFrom_scan_blank (Z : Fin k → ZTrack Symbol) {J : ℕ} (hV : (Z i).Valid J)
    (hj : (Z i).trig J (srcSide mv i) = J) (B : ℤ → Option (HSym k Symbol)) (pB : ℤ) :
    (hennieStearns tm).runFrom (C q mv i p out .scan (encA Z J none) B 0 pB) (zs J + 1) =
      C q mv i p out (.cr₁ false false) (encA Z J none) B (zs J - 1) pB := by
  rw [runFrom_add, runFrom_walk tm q mv i .scan p _ _ 0 pB out 1 0 (zs J) fun u hu => by
    simp only [SignType.coe_one, one_mul, zero_add, SignType.coe_zero, zero_mul, add_zero]
    rw [readA_encA_nat]
    rcases Nat.eq_zero_or_pos u with rfl | hu0
    · simp [aCell_zero, opTr, centerCell]
    · have hl := lvl_lt_of_lt_zs hu0 hu
      rw [aCell_of_lt hu0 hl]
      simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte, part_zoneCell,
        ZTrack.zone_of_lt_trig hV (show lvl u < (Z i).trig J (srcSide mv i) by omega),
        List.getElem?_nil, Option.isSome_none]]
  simp only [SignType.coe_one, one_mul, zero_add, SignType.coe_zero, zero_mul, add_zero]
  rw [runFrom_one, step_op, readA_encA_nat, aCell_of_le (one_le_zs J) (by rw [lvl_zs])]
  simp only [opTr, act_apply, Option.elim_none]
  congr 1
  simp

/-- The state after walking home. -/
def nextState (q : State) (mv : Fin k → SignType) (i : Fin k) : Next → HState k State
  | .gatherD => .op q mv i (.gatherD false)
  | .gatherS => .op q mv i (.gatherS false)
  | .writeS => .op q mv i (.writeS false)
  | .writeD => .op q mv i (.writeD false)
  | .scan => .op q mv i .scan
  | .crWalk => .op q mv i .crWalk
  | .done => afterOp q mv i

/-- **Walking work tape `0` home** from cell `m`, over cells that are not the center. -/
lemma runFrom_back (nx : Next) (A B : ℤ → Option (HSym k Symbol)) (m : ℕ) (pB : ℤ)
    (h0 : ∃ c, readA (A 0) = some c ∧ c.center = true)
    (h : ∀ n : ℕ, 1 ≤ n → n ≤ m → ∀ c, readA (A n) = some c → c.center = false) :
    (hennieStearns tm).runFrom (C q mv i p out (.back nx) A B m pB) (m + 1) =
      C q mv i p out (.backB nx) A B 0 pB := by
  rw [runFrom_add, runFrom_walk tm q mv i (.back nx) p _ _ m pB out (-1) 0 m fun u hu => by
    simp only [SignType.coe_neg_one, neg_one_mul, SignType.coe_zero, zero_mul, add_zero]
    have hn := h (m - u) (by omega) (by omega)
    rw [show (m : ℤ) + -(u : ℤ) = ((m - u : ℕ) : ℤ) by omega] at *
    rcases hc : readA (A ((m - u : ℕ) : ℤ)) with _ | c
    · rfl
    · simp [opTr, hn c hc]]
  obtain ⟨c, hc, hcc⟩ := h0
  simp only [SignType.coe_neg_one, neg_one_mul, SignType.coe_zero, zero_mul, add_zero,
    show (m : ℤ) + -(m : ℤ) = 0 by omega]
  rw [runFrom_one, step_op, hc]
  simp only [opTr, hcc, ↓reduceIte, act_apply, Option.elim_none]
  congr 1
  simp

/-- **Walking work tape `1` home** from cell `r`, over cells that are not the home cell. -/
lemma runFrom_backB (nx : Next) (A B : ℤ → Option (HSym k Symbol)) (pA : ℤ) (r : ℕ)
    (h0 : (readB (B 0)).home = true)
    (h : ∀ u : ℕ, 1 ≤ u → u ≤ r → (readB (B u)).home = false) :
    (hennieStearns tm).runFrom (C q mv i p out (.backB nx) A B pA r) (r + 1) =
      hcfg (some (nextState q mv i nx)) p A B pA 1 out := by
  rw [runFrom_add, runFrom_walk tm q mv i (.backB nx) p _ _ pA r out 0 (-1) r fun u hu => by
    simp only [SignType.coe_neg_one, neg_one_mul, SignType.coe_zero, zero_mul, add_zero]
    have hn := h (r - u) (by omega) (by omega)
    rw [show (r : ℤ) + -(u : ℤ) = ((r - u : ℕ) : ℤ) by omega]
    rcases readA (A pA) with _ | c <;> simp [opTr, hn]]
  simp only [SignType.coe_neg_one, neg_one_mul, SignType.coe_zero, zero_mul, add_zero,
    show (r : ℤ) + -(r : ℤ) = 0 by omega]
  rw [runFrom_one, step_op]
  have key : ∀ a : Option (ACell k Symbol), opTr q mv i (.backB nx) a (readB (B 0)) =
      act none 0 none 1 (some (nextState q mv i nx)) := by
    intro a
    rcases a with _ | c <;> cases nx <;> simp [opTr, h0, nextState]
  rw [key, act_apply]
  congr 1
  simp

end Turing.MultiTapeTM.HennieStearns
