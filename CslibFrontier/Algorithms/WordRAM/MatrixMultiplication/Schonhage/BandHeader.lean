/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Power.Rename
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandProgram
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Actual header loads, native powers and concrete band addresses

## Main results

* `BandPreparation.exec_powerCode`: exact reuse of the five-register native power routine.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Renaming the actual power routine has no instruction overhead and changes only its
accumulator, counter and constant-one register. -/
theorem exec_powerCode {w : ℕ} (v b n : Fin 96)
    (hinj : Function.Injective (powerRegisters v b n)) (B M : ℕ) (hB : 1 ≤ B)
    (x : Data 96) (hb : x.regs b = B) (hn : x.regs n = M)
    (hfit : Fits w (B ^ M + M + 2)) :
    ∃ y, ExecWithin w (powerCode v b n) x y (4 * M + 5) ∧
      y.regs v = B ^ M ∧ y.regs one = 1 ∧ y.mem = x.mem ∧
      (∀ i, i ≠ v → i ≠ counter → i ≠ one → y.regs i = x.regs i) := by
  obtain ⟨y, he, hv, _, ho, hm, -⟩ :=
    Power.exec_rename (powerRegisters v b n) hinj B M hB x hb hn hfit
  refine ⟨y, he, hv, ho, hm, fun i hv' hc ho' => he.regs_eq ?_⟩
  simp [Power.program, Power.body, Code.rename, Code.Preserves, Op.rename, Op.dest, Op.bin,
    powerRegisters, Power.value, Power.counter, Power.base, Power.exponent, Power.one,
    Ne.symm hv', Ne.symm hc, Ne.symm ho']

/-- Scalar parameters loaded from the three actual input headers and small constants. -/
structure BasicParameters (L m N : ℕ) (x : Data 96) : Prop where
  /-- Input depth. -/
  levels : x.regs levels = L
  /-- Input inner cardinality. -/
  inner : x.regs inner = m
  /-- Input matrix dimension. -/
  rows : x.regs rows = N
  /-- Constant zero. -/
  zero : x.regs zero = 0
  /-- Constant one. -/
  one : x.regs one = 1
  /-- Constant two. -/
  two : x.regs two = 2
  /-- Constant three. -/
  three : x.regs three = 3
  /-- Constant four. -/
  four : x.regs four = 4
  /-- Constant seven. -/
  seven : x.regs seven = 7
  /-- Constant ten. -/
  ten : x.regs ten = 10

/-- The global numerical budget bounds every final header power and its exponent. -/
theorem power_fits {w L m N : ℕ} (hfit : Fits w (wordBudget L m N))
    (b n : ℕ) (hb : b ≤ 10) (hn : n ≤ L) : Fits w (b ^ n + n + 2) := by
  have hp : b ^ n ≤ 10 ^ L :=
    (Nat.pow_le_pow_left hb _).trans (Nat.pow_le_pow_right (by decide) hn)
  have hpos : 1 ≤ 10 ^ L := Nat.one_le_pow L 10 (by decide)
  apply hfit.of_le
  unfold wordBudget
  nlinarith only [hp, hn, hpos, Nat.zero_le N, Nat.zero_le (N * D m),
    Nat.zero_le (2 ^ L), Nat.zero_le (2 * numBands L m N * 10 ^ L)]

/-- All header powers are computed by five actual native loops. Their register embeddings
are injective and their complete cost is linear in the original depth. -/
theorem exec_headerPowers {w L m N : ℕ} (hm : m ≤ L) (x : Data 96)
    (hx : BasicParameters L m N x) (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w headerPowers x y (16 * L + 26) ∧ BasicParameters L m N y ∧
      y.regs columns = D m ∧ y.regs outerSize = N0 L m ∧ y.regs masks = 2 ^ L ∧
      y.regs cells = 7 ^ L ∧ y.regs leaves = 10 ^ L ∧ y.mem = x.mem := by
  have hL : Fits w (1 ^ L + L + 2) := power_fits hfit 1 L (by decide) le_rfl
  simp only [one_pow] at hL
  refine WP.exists_execWithin ?_
  unfold headerPowers
  wram_call (exec_powerCode columns four inner (by decide) 4 m (by decide))
    [power_fits hfit 4 m (by decide) hm] with x1 ⟨hD, ho1, hm1, hf1⟩
  wram_exec *
  wram_call (exec_powerCode outerSize three temporary (by decide) 3 (L - m) (by decide))
    [power_fits hfit 3 (L - m) (by decide) (Nat.sub_le _ _)] with x3 ⟨hN0, ho3, hm3, hf3⟩
  wram_call (exec_powerCode masks two levels (by decide) 2 L (by decide))
    [power_fits hfit 2 L (by decide) le_rfl] with x4 ⟨hS2, ho4, hm4, hf4⟩
  wram_call (exec_powerCode cells seven levels (by decide) 7 L (by decide))
    [power_fits hfit 7 L (by decide) le_rfl] with x5 ⟨hS7, ho5, hm5, hf5⟩
  wram_call (exec_powerCode leaves ten levels (by decide) 10 L (by decide))
    [power_fits hfit 10 L (by decide) le_rfl] with y ⟨hS10, ho6, hm6, hf6⟩
  exact ⟨by omega, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    hS10, hm6.trans (hm5.trans (hm4.trans (hm3.trans hm1)))⟩

/-- Concrete computed powers and addresses after native header initialization. -/
structure HeaderPost (L m N : ℕ) (x : Data 96) : Prop where
  /-- Original scalar headers and constants. -/
  fixed : BasicParameters L m N x
  /-- Thin dimension. -/
  columns : x.regs columns = D m
  /-- Outer block dimension. -/
  outerSize : x.regs outerSize = N0 L m
  /-- Complete mask scan range. -/
  masks : x.regs masks = 2 ^ L
  /-- Flat input length of each band array. -/
  cells : x.regs cells = 7 ^ L
  /-- Flat output length of each band encoding. -/
  leaves : x.regs leaves = 10 ^ L
  /-- Original initialized prefix length. -/
  prefixSize : x.regs prefixSize = inputEnd m N
  /-- Protected original-input copy address. -/
  snapshot : x.regs snapshot = snapshotBase L m N
  /-- Dense inverse-table address. -/
  inverse : x.regs inverse = inverseBase L m N
  /-- Selected-mask forward-table address. -/
  table : x.regs table = tableBase L m N
  /-- Shared band-encoding output address. -/
  catalogue : x.regs catalogue = catalogueBase L m N

/-- Header parameters are loaded from real memory, all five powers are computed natively,
and every concrete address calculation is charged. Header zero and all unrelated cells may
contain arbitrary words; initialization reads only addresses one through three. -/
theorem exec_header {w L m N : ℕ} (hm : m ≤ L) (x : Data 96)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N)
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w header x y (16 * L + 49) ∧ HeaderPost L m N y ∧ y.mem = x.mem := by
  have h256 : Fits w 256 := hfit.of_le (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have h2 : 2 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have hlocal : Fits w (4 * (N * D m) + 8 * 10 ^ L + 16) := hfit.of_le (by
    unfold wordBudget
    nlinarith only [Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
      Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L), Nat.zero_le (2 * numBands L m N * 10 ^ L)])
  unfold header headerLoads headerLayout
  wram_exec [hL, hmemory, hN]
  wram_call (exec_headerPowers hm _ (by constructor <;> wram_simp) hfit)
    with z ⟨hbasic, hD, hN0, hS2, hS7, hS10, hzmem⟩
  wram_exec *
  refine ⟨?_, by wram_simp; exact hzmem⟩
  refine ⟨by regs_frame, by wram_simp [hD], by wram_simp [hN0], by wram_simp [hS2],
    by wram_simp [hS7], by wram_simp [hS10], ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    wram_simp [hD, hN0, hS2, hS7, hS10]
    dsimp only [catalogueBase, tableBase, inverseBase, snapshotBase, inputEnd,
      Encoding.scratchBase, Encoding.outputBase]
    omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
