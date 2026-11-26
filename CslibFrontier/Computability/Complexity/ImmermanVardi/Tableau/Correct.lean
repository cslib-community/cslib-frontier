/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.ImmermanVardi.Tableau.Step
import CslibFrontier.Computability.Machines.Turing.MultiTape.InputAt

/-!
# Correctness of the positive native tableau rules

The positive local rules compute the next native configuration exactly. The finite domain
must contain both input endmarkers and the next work-head position. No property of an
arbitrary recursive approximation is assumed: the monotonicity theorem applies to every row,
and correctness is proved separately on the rows of actual native configurations.

## Main results

* `read_row`, `situation_row`: positive read and situation predicates have native semantics.
* `elsewhere_row`: the positive replacement for head negation is exact on native rows.
* `rowStep_row`: the positive rules compute exactly the next native configuration.
-/

public section

namespace Cslib.Complexity.ImmermanVardi.Tableau

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature

variable {m B : ℕ} {State : Type} {input : List Bool} {cfg : Cfg m Bool State input}

private theorem exists_offset_eq {B : ℕ} {z : ℤ} (hz : |z| < B) :
    ∃ (s : Bool) (a : Fin B), offset s a = z := by
  rw [abs_lt] at hz
  by_cases hp : 0 ≤ z
  · exact ⟨true, ⟨z.toNat, by omega⟩, by simp only [offset, ↓reduceIte]; omega⟩
  · exact ⟨false, ⟨(-z).toNat, by omega⟩,
      by simp only [offset, Bool.false_eq_true, ↓reduceIte]; omega⟩

/-- The positive read rule recovers the symbol under a head inside the finite domain. -/
theorem read_row (hb : ∀ i, |cfg.workTapePos i| < B) (i : Fin m) (s : Option Bool) :
    read (row (B := B) cfg) i s ↔ (Feature.read i s).Holds cfg := by
  simp only [read, row, Tag.feature, Feature.Holds, Cfg.workTapeSymbols]
  constructor
  · rintro ⟨a, ⟨hh, hc⟩ | ⟨hh, hc⟩⟩ <;> rwa [hh]
  · intro hs
    obtain ⟨sign, a, ha⟩ := exists_offset_eq (hb i)
    cases sign <;> exact ⟨a, by simp_all⟩

/-- Positive situation predicates agree with the native situation. -/
theorem situation_row (hn : input.length + 1 < B) (hb : ∀ i, |cfg.workTapePos i| < B)
    (y : Situation m State) (a : Fin B) :
    situation input (row cfg) y a ↔ (Feature.sit y).Holds cfg := by
  rw [situation, holds_sit_iff]
  simp only [row, Tag.feature]
  refine and_congr Iff.rfl (and_congr ?_ (forall_congr' fun i => read_row hb i _))
  simp only [holds_inPos, holds_inRead, Cfg.inputSymbol_eq_inputAt]
  exact ⟨fun ⟨j, hj, hs⟩ => hj ▸ hs,
    fun hs => ⟨⟨cfg.inputPos.val, cfg.inputPos.isLt.trans_le hn⟩, rfl, hs⟩⟩

/-- A positively witnessed other head position is equivalent to head inequality. -/
theorem elsewhere_row (hb : ∀ i, |cfg.workTapePos i| < B)
    (i : Fin m) (sign : Bool) (a : Fin B) :
    elsewhere (row cfg) i sign a ↔ ¬(Feature.head i (offset sign a)).Holds cfg := by
  simp only [elsewhere, row, Tag.feature, Feature.Holds]
  constructor
  · rintro ⟨b, ⟨hb', hba⟩ | ⟨hb', hba⟩⟩ hpos
    · apply hba; apply Fin.ext
      cases sign <;> simp only [offset, Bool.false_eq_true, ↓reduceIte] at hb' hpos <;> omega
    · apply hba
      cases sign <;> simp only [offset, Bool.false_eq_true, Bool.not_true,
        Bool.not_false, ↓reduceIte] at hb' hpos <;> omega
  · intro hne
    obtain ⟨s, b, hb'⟩ := exists_offset_eq (hb i)
    refine ⟨b, ?_⟩
    rcases Bool.eq_or_eq_not s sign with rfl | rfl
    · exact .inl ⟨hb'.symm, fun h => hne (h ▸ hb'.symm)⟩
    · refine .inr ⟨hb'.symm, fun h0 => hne ?_⟩
      cases sign <;> simp only [offset, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] at hb' ⊢ <;> omega

/-- The positive input-head predecessor rule describes the native clamped move. -/
theorem inputPrev_row (hn : input.length + 1 < B) (d : SignType) (a : Fin B) :
    inputPrev input (row cfg) d a ↔
      moveInputPosNat input.length cfg.inputPos.val d = a.val := by
  have hp := cfg.inputPos.isLt
  cases d <;> simp only [inputPrev, row, Tag.feature, Feature.Holds,
    moveInputPosNat, SignType.zero_eq_zero, SignType.neg_eq_neg_one, SignType.pos_eq_one,
    SignType.coe_zero, SignType.coe_neg_one, SignType.coe_one]
  · omega
  · constructor
    · rintro (⟨ha, hh⟩ | ⟨b, hb, hh⟩) <;> omega
    · intro hmove
      by_cases hz : cfg.inputPos.val = 0
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨⟨cfg.inputPos.val, by omega⟩, by dsimp; omega, rfl⟩
  · simp only [ne_eq, inputAt_eq_none_iff, not_or]
    constructor
    · rintro (⟨ha, hh, hp'⟩ | ⟨b, hb, hp', hx⟩) <;> omega
    · intro hmove
      by_cases he : cfg.inputPos.val = input.length + 1
      · exact Or.inl ⟨by omega, Or.inr (by omega), by omega⟩
      · exact Or.inr ⟨⟨cfg.inputPos.val, by omega⟩, by dsimp; omega, rfl, by dsimp; omega⟩

private theorem headPrev_out {B : ℕ} {z : ℤ} (hz : |z| + 1 < B) (a : Fin B) :
    ((a.val = 0 ∧ ∃ b : Fin B, b.val = 1 ∧ z = -(b.val : ℤ)) ∨
      ∃ b : Fin B, b.val + 1 = a.val ∧ z = (b.val : ℤ)) ↔ z + 1 = (a.val : ℤ) := by
  have := abs_lt.mp (by omega : |z| < (B : ℤ) - 1)
  constructor
  · rintro (⟨ha, b, hb, hp⟩ | ⟨b, hb, hp⟩) <;> omega
  · intro hmove
    by_cases ha : a.val = 0
    · exact Or.inl ⟨ha, ⟨1, by omega⟩, rfl, by dsimp; omega⟩
    · exact Or.inr ⟨⟨a.val - 1, by omega⟩, by dsimp; omega, by dsimp; omega⟩

private theorem headPrev_in {B : ℕ} {z : ℤ} (hz : |z| + 1 < B) (a : Fin B) :
    (∃ b : Fin B, a.val + 1 = b.val ∧ z = (b.val : ℤ)) ↔ z + -1 = (a.val : ℤ) := by
  have := abs_lt.mp (by omega : |z| < (B : ℤ) - 1)
  constructor
  · rintro ⟨b, hb, hp⟩; omega
  · intro hmove; exact ⟨⟨a.val + 1, by omega⟩, rfl, by dsimp; omega⟩

/-- The positive work-head predecessor rule describes the native signed move. -/
theorem headPrev_row (hb : ∀ i, |cfg.workTapePos i| + 1 < B)
    (i : Fin m) (sign : Bool) (d : SignType) (a : Fin B) :
    headPrev (row cfg) i sign d a ↔
      cfg.workTapePos i + (d : ℤ) = offset sign a := by
  have hbi := hb i
  have hneg : |-cfg.workTapePos i| + 1 < B := by rwa [abs_neg]
  cases sign <;> cases d <;>
    simp only [headPrev, row, Tag.feature, Feature.Holds, offset, Bool.false_eq_true,
      Bool.not_false, Bool.not_true, ↓reduceIte,
      SignType.zero_eq_zero, SignType.neg_eq_neg_one, SignType.pos_eq_one,
      SignType.coe_zero, SignType.coe_neg_one, SignType.coe_one, neg_zero, neg_neg,
      add_zero]
  · refine Iff.trans ?_ (by omega : -cfg.workTapePos i + 1 = a.val ↔ _)
    simpa only [neg_eq_iff_eq_neg, neg_neg] using headPrev_out hneg a
  · refine Iff.trans ?_ (by omega : -cfg.workTapePos i + -1 = a.val ↔ _)
    simpa only [neg_eq_iff_eq_neg] using headPrev_in hneg a
  · exact headPrev_in hbi a
  · exact headPrev_out hbi a

variable [Finite State] (tm : MultiTapeTM m Bool State)

/-- The positive rules produce exactly the row of the next native configuration. -/
theorem rowStep_row (hn : input.length + 1 < B)
    (hb : ∀ i, |cfg.workTapePos i| + 1 < B) (q : Tag m State) (a : Fin B) :
    rowStep tm input (row cfg) q a ↔ row (tm.step cfg) q a := by
  classical
  let _ := Fintype.ofFinite State
  have hb' : ∀ i, |cfg.workTapePos i| < B := fun i => by have := hb i; omega
  cases q with
  | state q =>
    simp only [rowStep, situation_row hn hb', row, Tag.feature,
      holds_step_state_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  | out o =>
    simp only [rowStep, situation_row hn hb', row, Tag.feature, holds_step_out_iff,
      Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Prod.exists]
  | inPos =>
    simp only [rowStep, situation_row hn hb', inputPrev_row hn,
      row, Tag.feature, holds_inPos]
    cases hq : cfg.state with
    | none => simp [hq, not_holds_sit hq]
    | some q =>
      simp [holds_state, hq, holds_sit_iff_eq hq, step_eq_apply tm hq,
        Action.apply_inputPos, val_moveInputPos_eq_moveInputPosNat]
  | head i sign =>
    simp only [rowStep, situation_row hn hb', headPrev_row hb,
      row, Tag.feature, holds_head]
    cases hq : cfg.state with
    | none => simp [hq, not_holds_sit hq]
    | some q =>
      simp [holds_state, hq, holds_sit_iff_eq hq, step_eq_apply tm hq,
        Action.apply_workTapePos]
  | cell i sign s =>
    simp only [rowStep, situation_row hn hb', elsewhere_row hb', row, Tag.feature,
      holds_step_cell_iff, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and, Prod.exists]

end Cslib.Complexity.ImmermanVardi.Tableau
