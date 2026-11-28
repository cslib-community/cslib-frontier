/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPopulation

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Tactic.UpdateSimp

/-!
# Charged materialization of the subset tables

## Main definitions

* `BandPreparation.tableStep`: the exact memory writes made by one table iteration.

## Main results

* `BandPreparation.exec_tableWrite`: actual inverse/forward table stores and counter updates.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open MaskTable

/-- The inverse word is initialized even for an unselected mask. Selected masks also write
one forward-table cell. This is only a mathematical description of the two native stores. -/
def tableStep (L m inv tab t : ℕ) (μ : ℕ → ℕ) : ℕ → ℕ :=
  let μ' := Function.update μ (inv + t) (lookup L m t)
  if lookup L m t = 0 then μ' else Function.update μ' (tab + prefixCount L m t) t

/-- The part of both tables computed after visiting `t` masks. The outside frame permits
arbitrary caller memory, including future query inputs and scratch regions. -/
structure TablesPrefix (L m inv tab t : ℕ) (initial current : ℕ → ℕ) : Prop where
  /-- Every visited inverse word has been initialized. -/
  inverse : ∀ a < t, current (inv + a) = lookup L m a
  /-- Every selected visited mask has been placed at its prefix rank. -/
  forward : ∀ a < t, lookup L m a ≠ 0 → current (tab + prefixCount L m a) = a
  /-- Only the two explicitly reserved table blocks may change. -/
  frame : ∀ a, ¬(inv ≤ a ∧ a < inv + 2 ^ L) → ¬(tab ≤ a ∧ a < tab + 2 ^ L) →
    current a = initial a

/-- Empty scan prefix, with no initialized-memory assumption. -/
theorem TablesPrefix.zero (L m inv tab : ℕ) (μ : ℕ → ℕ) :
    TablesPrefix L m inv tab 0 μ μ :=
  ⟨fun _ h => (Nat.not_lt_zero _ h).elim,
    fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩

/-- The actual two stores extend the initialized table prefix by one mask. -/
theorem TablesPrefix.step {L m inv tab t : ℕ} {μ μ' : ℕ → ℕ}
    (h : TablesPrefix L m inv tab t μ μ') (ht : t < 2 ^ L)
    (hsep : inv + 2 ^ L ≤ tab) :
    TablesPrefix L m inv tab (t + 1) μ (tableStep L m inv tab t μ') := by
  have hr : prefixCount L m t < 2 ^ L := (prefixCount_le L m t).trans_lt ht
  constructor
  · intro a ha
    by_cases hat : a = t
    · subst a; update_simp [tableStep]
    · update_simp [tableStep]; exact h.inverse a (by omega)
  · intro a ha hselected
    by_cases hat : a = t
    · subst a; update_simp [tableStep]
    · have haold : a < t := by omega
      have hpop := (lookup_ne_zero_iff L m a).mp hselected |>.2.1
      have hless := prefixCount_lt hpop haold
      update_simp [tableStep]
      exact h.forward a haold hselected
  · intro a hi hf
    update_simp [tableStep]
    exact h.frame a hi hf

/-- Execute the stores after the population loop. The code neither searches a supplied
table nor receives a table-validity certificate. -/
theorem exec_tableWrite {w : ℕ} (L m inv tab t : ℕ) (x : Data 96)
    (ht : t < 2 ^ L) (hinv : x.regs inverse = inv) (htab : x.regs table = tab)
    (hmask : x.regs mask = t) (hrank : x.regs rank = prefixCount L m t)
    (hpop : x.regs population = MaskTable.population L t) (hm : x.regs inner = m)
    (hsq : x.regs square = K0 L m * K0 L m)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hfit : Fits w (inv + tab + 2 ^ L + 4)) :
    ∃ y, ExecWithin w tableWrite x y 10 ∧ y.mem = tableStep L m inv tab t x.mem ∧
      y.regs mask = t + 1 ∧ y.regs rank = prefixCount L m (t + 1) ∧
      (∀ i, i ≠ address → i ≠ temporary → i ≠ mask → i ≠ rank → y.regs i = x.regs i) := by
  have hbound := prefixCount_le L m t
  suffices ∃ y, ExecWithin w tableWrite x y 10 ∧ y.mem = tableStep L m inv tab t x.mem ∧
      y.regs mask = t + 1 ∧ y.regs rank = prefixCount L m (t + 1) by
    obtain ⟨y, he, hm', hmt, hrk⟩ := this
    refine ⟨y, he, hm', hmt, hrk, fun i ha htmp hm_ne hr_ne => he.regs_eq ?_⟩
    revert i ha htmp hm_ne hr_ne
    simp only [tableWrite, Code.Preserves, Op.dest, Op.bin]
    decide
  wram_exec * [tableWrite]
  · rename_i hp
    wram_simp [tableStep, lookup, ht, hp, hc, prefixCount_succ, Function.update_idem]
  · rename_i hp
    wram_simp [tableStep, lookup, ht, hp, hc, prefixCount_succ]
  · wram_simp [tableStep, lookup, ht, hc, prefixCount_succ, hrank, false_and]

/-- Persistent scalar parameters read by the table loops. These are register contents only;
there is no execution, fit or cost assumption in this postcondition. -/
structure TableParameters (L m inv tab : ℕ) (x : Data 96) : Prop where
  /-- Original depth. -/
  levels : x.regs levels = L
  /-- Original inner cardinality. -/
  inner : x.regs inner = m
  /-- Computed complete binary-mask range. -/
  masks : x.regs masks = 2 ^ L
  /-- Inverse-table base. -/
  inverse : x.regs inverse = inv
  /-- Forward-table base. -/
  table : x.regs table = tab
  /-- Computed number of selected masks. -/
  square : x.regs square = K0 L m * K0 L m
  /-- Constant zero. -/
  zero : x.regs zero = 0
  /-- Constant one. -/
  one : x.regs one = 1
  /-- Constant two. -/
  two : x.regs two = 2

/-- The complete native scan computes both tables, with all inner population scans and
outer controls charged. Outside memory may contain arbitrary caller data. -/
theorem exec_tables {w : ℕ} (L m inv tab : ℕ) (x : Data 96)
    (hx : TableParameters L m inv tab x) (hsep : inv + 2 ^ L ≤ tab)
    (hfit : Fits w (inv + tab + 2 ^ L + L + 4)) :
    ∃ y, ExecWithin w tablesCode x y ((6 * L + 17) * 2 ^ L + 4) ∧
      TableParameters L m inv tab y ∧
      (∀ a < 2 ^ L, y.mem (inv + a) = lookup L m a) ∧
      (∀ gh : Fin (K0 L m) × Fin (K0 L m),
        y.mem (tab + (pairRank gh).val) = (selectedMask gh).val) ∧
      (∀ a, ¬(inv ≤ a ∧ a < inv + 2 ^ L) → ¬(tab ≤ a ∧ a < tab + 2 ^ L) →
        y.mem a = x.mem a) := by
  let P (j : ℕ) (y : Data 96) : Prop :=
    TableParameters L m inv tab y ∧
      y.regs rank = prefixCount L m j ∧
      TablesPrefix L m inv tab j x.mem y.mem
  have hb (y : Data 96) (hy : P (y.regs mask) y) (htlt : y.regs mask < 2 ^ L) :
      ∃ z, ExecWithin w tableBody y z (6 * L + 15) ∧ P (y.regs mask + 1) z ∧
        z.regs mask = y.regs mask + 1 := by
    obtain ⟨hp, hrank, hmem⟩ := hy
    refine WP.exists_execWithin ?_
    unfold tableBody
    wram_call (exec_population L (y.regs mask) y hp.levels rfl hp.one hp.two
      (hfit.of_le (by omega))) with u ⟨hpop, humem, huf⟩
    wram_call (exec_tableWrite (w := w) L m inv tab (y.regs mask)) [htlt]
      with z ⟨hzmem, hzt, hzr, _⟩
    refine ⟨by omega, ⟨by regs_frame, hzr, ?_⟩, hzt⟩
    rw [hzmem, humem]
    exact hmem.step htlt hsep
  wram_exec * [tablesCode]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1.masks) hb
    (by wram_simp; exact Nat.zero_le _)
    (by refine ⟨by regs_frame, by wram_simp [prefixCount_zero],
      by wram_simp; exact TablesPrefix.zero L m inv tab x.mem⟩))
    with y ⟨⟨hyp, _, hymem⟩, ht⟩
  refine ⟨by wram_simp [ht]; nlinarith, hyp, hymem.inverse, ?_, hymem.frame⟩
  intro gh
  have hlookup : lookup L m (selectedMask gh).val ≠ 0 := by rw [lookup_selectedMask]; omega
  simpa only [prefixCount_selectedMask] using
    hymem.forward (selectedMask gh).val (selectedMask gh).isLt hlookup

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
