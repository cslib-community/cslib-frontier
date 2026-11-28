/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.Randomized
public import CslibFrontier.Computability.WordRAM.Subroutine
public import CslibFrontier.Computability.WordRAM.Word
public import CslibFrontier.Computability.WordRAM.Randomized.Expected
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Tactic.FinIndex
import Mathlib.Data.Finset.Sort

/-!
# Simulating Word-RAM Programs in the Adaptive Cell-Probe Model

This file builds the computational simulation bridge (`Cslib.CellProbe`) from deterministic,
finite-tree randomized, and unbounded Las Vegas Word-RAM executions (`Cslib.WordRAM`) to adaptive
deterministic cell-probe trees (`ProbeTree`; [Miltersen1999], §1.2, pp. 1–2) and internal-coin
randomized cell-probe trees (`RandProbeTree`; coin-fixing reduction after [Yao1977]).

On a `w`-bit Word RAM with `r` registers and contiguous memory footprint `[base, base + S)`, two
model differences require explicit accounting in a formal simulation:
1. **Persistent registers across operations:** A cell-probe scheme keeps state between operations
   solely in `Mem cells wCell` (`Fin cells → Fin (2 ^ wCell)`), with no registers surviving across
   operation boundaries. Given an input-register mask `input : Fin r → Bool` (such as `P.input` on
   `WordRAM.SubroutineCode B r k_init`), only the `persCount input` persistent registers with
   `input i = false` survive between calls:
   * **Standard `w`-bit layout (`standardLayout`):** Allocates `S + persCount input` cells of width
     `w` (`0` extra cells and `0` extra probes when `∀ i, input i = true`), reloading persistent
     registers in `persCount input` reads and spilling them at halt in `persCount input` writes
     (`2 * persCount input` additive probes per operation).
   * **Wide-cell single-spill layout (`wideLayout`):** Packs all `persCount input` persistent
     registers in base `2 ^ w` into `1` cell of width
     `wideWidth input w := max (persCount input) 1 * w` over `S + 1` cells, paying `0` extra probes
     when `persCount input = 0` and `2` extra probes (`1` read + `1` write) whenever
     `persCount input > 0`, independent of `r`.
2. **Unallocated reads and unbounded Las Vegas loops:**
   * Replacing Word-RAM memory outside `[base, base + S)` by `0` (`zeroOutside base S`) keeps loads
     and stores outside `[base, base + S)` in a pure-Lean intra-operation map at `0` probe cost;
     when `Modifies (Block.mk base S).footprint` holds at halt, outside memory returns to `0` at
     every operation boundary.
   * Writes inside `[base, base + S)` are buffered in pure Lean during a clocked `K`-step run and
     flushed only at halt, so `reads + flushedWrites ≤ continuingSteps` and cell memory remains
     untouched if execution is still active at step `K`. On that `> K` tail event (probability
     tending to `0` as `K → ∞` whenever `expectedTime < ⊤`), the simulator reads all `S` data
     cells, selects a reachable halting post-state in pure Lean from `haltedLim` (`> 0` by
     almost-sure halting, hence in the target support), and writes the resulting packed memory
     (`2 * S + regCells` extra probes on the tail), preserving **100% zero-error support
     correctness** at finite tree depth while achieving expected probes `≤ T + overhead + η` for any
     `η > 0`.

While [Miltersen1999], §1.2, p. 2 notes only that cell-probe lower bounds transfer up to a
constant factor to unit-cost RAMs of the same word size whose instructions touch a constant number
of registers, the `zeroOutside` footprint framing, multi-register `persistentRegCount` / wide-cell
spill layouts, intra-operation write buffering, and finite-horizon Las Vegas truncation are local
library constructions connecting `Cslib.WordRAM` to `Cslib.CellProbe`. For data-structure `Impl`
bridges and contrapositive lower-bound transfer corollaries, see
`CslibFrontier.DataStructure.CellProbe.OfWordRAM`.

## Main definitions

* `Cslib.CellProbe.persRegs`, `Cslib.CellProbe.persCount`,
  `Cslib.CellProbe.persistentRegCount`: persistent register set and count (`input i = false`).
* `Cslib.CellProbe.zeroOutside`: zero Word-RAM memory outside `[base, base + S)`.
* `Cslib.CellProbe.packMem`, `Cslib.CellProbe.unpackData`:
  standard `w`-bit packing between `WordRAM.Data r` and `Mem (S + persCount input) w`.
* `Cslib.CellProbe.wideWidth`, `Cslib.CellProbe.wideSubroutineWidth`,
  `Cslib.CellProbe.DataCellsBounded`, `Cslib.CellProbe.packMemWide`,
  `Cslib.CellProbe.unpackDataWide`: single-cell base-`2 ^ w` register packing over `S + 1` cells
  of width `max (persCount input) 1 * w`.
* `Cslib.CellProbe.RegLayout`, `Cslib.CellProbe.standardLayout`, `Cslib.CellProbe.wideLayout`:
  unified cell-layout interface shared by deterministic and randomized simulators.
* `Cslib.CellProbe.simProgDet`, `Cslib.CellProbe.simProgInitDet`,
  `Cslib.CellProbe.simProgDetAuto`, `Cslib.CellProbe.simProgRand`: clocked and automatic-fuel
  deterministic (`ProbeTree`) and buffered randomized (`RandProbeTree`) flat-program simulators.
* `Cslib.CellProbe.ExecProgramDist`: distributional execution contract for flat `WordRAM.Program`s.

## Main results

* `Cslib.CellProbe.persistentRegCount_eq_zero_of_all_input`,
  `Cslib.CellProbe.persistentRegCount_le`: zero-overhead specialization and register-count bound.
* `Cslib.CellProbe.simProgDet_spec`, `Cslib.CellProbe.simProgDetAuto_spec`,
  `Cslib.CellProbe.simExecWithin`, `Cslib.CellProbe.simExecWithinWide`: deterministic flat-program
  and structured `ExecWithin` simulation in `≤ T + 2 * r_pers` (or `≤ T + 2` wide) probes.
* `Cslib.CellProbe.simExecRand`, `Cslib.CellProbe.simExecRandWide`: exact-distribution finite-tree
  `ExecRand` simulation in `RandProbeTree` with zero `η` slack.
* `Cslib.CellProbe.ExecProgramDist.haltedLim_eq`,
  `Cslib.CellProbe.execProgramDist_of_execCodeDist`,
  `Cslib.CellProbe.simProgRand_lasVegas_spec`, `Cslib.CellProbe.exists_uniform_cutoff`:
  exact halting-law identification, compilation of `ExecCodeDist` to `ExecProgramDist`, and
  uniform-horizon buffered Las Vegas simulation with zero-error support preservation and arbitrary
  `η > 0` expected-probe slack.

## References

* [P. B. Miltersen, *Cell Probe Complexity — a Survey*, §1.2][Miltersen1999]
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
-/

public section

namespace Cslib.CellProbe

open Cslib.WordRAM Cslib.Probability
open scoped ENNReal

/-! ### 1. Persistent register accounting -/

/-- Subset of registers `i : Fin r` that persist across calls (`input i = false`). -/
@[expose] def persRegs {r : ℕ} (input : Fin r → Bool) : Finset (Fin r) :=
  Finset.univ.filter fun i => !input i

/-- Number of persistent registers (`input i = false`) under calling-convention mask `input`. -/
@[expose] def persCount {r : ℕ} (input : Fin r → Bool) : ℕ :=
  (persRegs input).card

@[simp]
theorem mem_persRegs {r : ℕ} {input : Fin r → Bool} {i : Fin r} :
    i ∈ persRegs input ↔ input i = false := by
  simp [persRegs]

@[simp]
theorem persCount_eq_zero_of_all_input {r : ℕ} {input : Fin r → Bool}
    (h : ∀ i, input i = true) : persCount input = 0 := by
  simp [persCount, persRegs, h]

theorem persCount_le {r : ℕ} (input : Fin r → Bool) : persCount input ≤ r :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin r)

/-- Number of persistent registers (`P.input i = false`) of a `WordRAM.SubroutineCode`. -/
@[expose] def persistentRegCount {B : Basis} {r k_init : ℕ} (P : SubroutineCode B r k_init) : ℕ :=
  (Finset.univ.filter fun i : Fin r => !P.input i).card

theorem persistentRegCount_eq_persCount {B : Basis} {r k_init : ℕ}
    (P : SubroutineCode B r k_init) : persistentRegCount P = persCount P.input := by
  rfl

@[simp]
theorem persistentRegCount_eq_zero_of_all_input {B : Basis} {r k_init : ℕ}
    {P : SubroutineCode B r k_init} (h : ∀ i, P.input i = true) :
    persistentRegCount P = 0 :=
  persCount_eq_zero_of_all_input h

theorem persistentRegCount_le {B : Basis} {r k_init : ℕ} (P : SubroutineCode B r k_init) :
    persistentRegCount P ≤ r :=
  persCount_le P.input

/-- Canonical order-preserving enumeration of persistent registers
`Fin (persCount input) → Fin r`. -/
def persReg {r : ℕ} (input : Fin r → Bool) (k : Fin (persCount input)) : Fin r :=
  ((persRegs input).orderIsoOfFin rfl k).val

theorem persReg_input_eq_false {r : ℕ} (input : Fin r → Bool) (k : Fin (persCount input)) :
    input (persReg input k) = false :=
  mem_persRegs.mp ((persRegs input).orderIsoOfFin rfl k).property

theorem persReg_injective {r : ℕ} (input : Fin r → Bool) :
    Function.Injective (persReg input) := fun _ _ h =>
  ((persRegs input).orderIsoOfFin rfl).injective (Subtype.ext h)

/-- Inverse index of a persistent register `i : Fin r` (`input i = false`) in
`Fin (persCount input)`. -/
def persIdx {r : ℕ} (input : Fin r → Bool) (i : Fin r) (hi : input i = false) :
    Fin (persCount input) :=
  ((persRegs input).orderIsoOfFin rfl).symm ⟨i, mem_persRegs.mpr hi⟩

@[simp]
theorem persReg_persIdx {r : ℕ} (input : Fin r → Bool) (i : Fin r) (hi : input i = false) :
    persReg input (persIdx input i hi) = i := by
  simp [persReg, persIdx]

@[simp]
theorem persIdx_persReg {r : ℕ} (input : Fin r → Bool) (k : Fin (persCount input)) :
    persIdx input (persReg input k) (persReg_input_eq_false input k) = k :=
  OrderIso.symm_apply_apply ((persRegs input).orderIsoOfFin rfl) k

/-! ### 2. `zeroOutside` framing, standard & wide-cell memory packing, and `RegLayout` -/

/-- Replace Word-RAM memory outside `[base, base + S)` with `0`, preserving registers and
`[base, base + S)`. -/
@[expose] def zeroOutside {r : ℕ} (base S : ℕ) (x : Data r) : Data r where
  regs := x.regs
  mem a := if base ≤ a ∧ a < base + S then x.mem a else 0

@[simp]
theorem zeroOutside_regs {r : ℕ} (base S : ℕ) (x : Data r) :
    (zeroOutside base S x).regs = x.regs :=
  rfl

theorem zeroOutside_mem_of_mem_footprint {r : ℕ} {base S a : ℕ} (x : Data r)
    (ha : a ∈ (Block.mk base S).footprint) :
    (zeroOutside base S x).mem a = x.mem a := by
  have hown : base ≤ a ∧ a < base + S := Block.mem_footprint.mp ha
  simp [zeroOutside, hown]

theorem zeroOutside_mem_of_not_owns {r : ℕ} {base S a : ℕ} (x : Data r)
    (ha : ¬(base ≤ a ∧ a < base + S)) :
    (zeroOutside base S x).mem a = 0 := by
  simp [zeroOutside, ha]

theorem zeroOutside_bounded {r w : ℕ} (base S : ℕ) {x : Data r} (hx : x.Bounded w) :
    (zeroOutside base S x).Bounded w := by
  refine ⟨hx.1, fun a => ?_⟩
  dsimp only [zeroOutside]
  split_ifs
  exacts [hx.2 a, fits_zero w]

/-- Pack `x : Data r` (`[base, base + S)` plus persistent registers) into
`Mem (S + persCount input) w`. -/
@[expose] def packMem {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) (x : Data r) :
    Mem (S + persCount input) w := fun c =>
  if hc : c.val < S then
    wordOfNat w (x.mem (base + c.val))
  else
    wordOfNat w (x.regs (persReg input ⟨c.val - S, by omega⟩))

/-- Unpack `m : Mem (S + persCount input) w` with caller-supplied input registers `argRegs` into
`Data r` (with `0` outside `[base, base + S)`). -/
@[expose] def unpackData {r : ℕ} (input : Fin r → Bool) (argRegs : Fin r → ℕ) (base S w : ℕ)
    (m : Mem (S + persCount input) w) : Data r where
  regs i :=
    if hi : input i = true then argRegs i
    else (m (Fin.natAdd S (persIdx input i (Bool.eq_false_iff.mpr hi)))).val
  mem a :=
    if ha : base ≤ a ∧ a < base + S then
      (m (Fin.castAdd (persCount input) ⟨a - base, by omega⟩)).val
    else 0

theorem unpackData_bounded {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + persCount input) w) :
    (unpackData input argRegs base S w m).Bounded w := by
  refine ⟨fun i => ?_, fun a => ?_⟩ <;> dsimp only [unpackData] <;> split_ifs with h
  exacts [harg i h, (m _).isLt, (m _).isLt, fits_zero w]

theorem unpackData_packMem_regs {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} {x : Data r} (hx : x.Bounded w) (i : Fin r) :
    (unpackData input argRegs base S w (packMem input base S w x)).regs i =
      if input i then argRegs i else x.regs i := by
  dsimp only [unpackData]
  split_ifs with hi
  · rfl
  · simp [packMem, wordOfNat_val_of_lt (hx.1 i)]

theorem unpackData_packMem_mem {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} {x : Data r} (hx : x.Bounded w) (a : ℕ) :
    (unpackData input argRegs base S w (packMem input base S w x)).mem a =
      (zeroOutside base S x).mem a := by
  dsimp only [unpackData, zeroOutside]
  split_ifs with ha
  · simp [packMem, show a - base < S by omega, show base + (a - base) = a by omega,
      wordOfNat_val_of_lt (hx.2 a)]
  · rfl

/-! #### Wide-cell base-`2 ^ w` persistent-register codec (`wideLayout`) -/

/-- Wide cell bit-width `max (persCount input) 1 * w` packing all persistent registers into `1`
cell while remaining at least `w` bits wide when `persCount input = 0`. -/
@[expose] def wideWidth {r : ℕ} (input : Fin r → Bool) (w : ℕ) : ℕ :=
  max (persCount input) 1 * w

/-- Subroutine specialization `max (persistentRegCount P) 1 * w` of `wideWidth`. -/
@[expose] def wideSubroutineWidth {B : Basis} {r k_init : ℕ}
    (P : SubroutineCode B r k_init) (w : ℕ) : ℕ :=
  max (persistentRegCount P) 1 * w

theorem le_wideWidth {r : ℕ} (input : Fin r → Bool) (w : ℕ) : w ≤ wideWidth input w :=
  Nat.le_mul_of_pos_left w (lt_max_of_lt_right Nat.one_pos)

theorem persCount_mul_le_wideWidth {r : ℕ} (input : Fin r → Bool) (w : ℕ) :
    persCount input * w ≤ wideWidth input w :=
  Nat.mul_le_mul_right w (le_max_left _ _)

/-- Encode `k` `w`-bit words as a single natural number `< 2 ^ (k * w)` in base `2 ^ w`. -/
def packDigits : (k w : ℕ) → (Fin k → Fin (2 ^ w)) → ℕ
  | 0, _, _ => 0
  | k + 1, w, f => (f 0).val + 2 ^ w * packDigits k w (fun j => f j.succ)

theorem packDigits_lt : ∀ (k w : ℕ) (f : Fin k → Fin (2 ^ w)), packDigits k w f < 2 ^ (k * w)
  | 0, w, _ => by simp [packDigits]
  | k + 1, w, f => by
    have hlo : (f 0).val < 2 ^ w := (f 0).isLt
    have hhi := Nat.mul_le_mul_left (2 ^ w)
      (Nat.succ_le_of_lt (packDigits_lt k w fun j => f j.succ))
    rw [packDigits, show (k + 1) * w = w + k * w by ring, Nat.pow_add]
    linarith

/-- Decode `k` `w`-bit words in base `2 ^ w` from a natural number `val`. -/
def unpackDigits : (k w val : ℕ) → Fin k → Fin (2 ^ w)
  | 0, _, _ => Fin.elim0
  | k + 1, w, val =>
    Fin.cons ⟨val % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩ (unpackDigits k w (val / 2 ^ w))

@[simp]
theorem unpackDigits_packDigits :
    ∀ (k w : ℕ) (f : Fin k → Fin (2 ^ w)), unpackDigits k w (packDigits k w f) = f
  | 0, _, f => funext fun j => j.elim0
  | k + 1, w, f => by
    have hlo := (f 0).isLt
    funext j
    refine j.cases (Fin.ext ?_) (fun i => ?_)
    · simp [packDigits, unpackDigits, Nat.mod_eq_of_lt hlo]
    · simp [packDigits, unpackDigits, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
        Nat.div_eq_of_lt hlo, unpackDigits_packDigits k w]

theorem packDigits_eq_zero_of_zero {k w : ℕ} (hk : k = 0) (f : Fin k → Fin (2 ^ w)) :
    packDigits k w f = 0 := by
  subst hk
  rfl

/-- Invariant asserting that data cells `0 .. S - 1` of a wide-cell memory hold `w`-bit values. -/
@[expose] def DataCellsBounded (S w wCell : ℕ) (m : Mem (S + 1) wCell) : Prop :=
  ∀ j : Fin S, (m (Fin.castAdd 1 j)).val < 2 ^ w

/-- Pack `x : Data r` into `Mem (S + 1) (wideWidth input w)`: cells `0 .. S - 1` hold
`x.mem (base + j)`, and cell `S` holds all `persCount input` persistent registers in base `2 ^ w`.
-/
@[expose] def packMemWide {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) (x : Data r) :
    Mem (S + 1) (wideWidth input w) := fun c =>
  if hc : c.val < S then
    ⟨(wordOfNat w (x.mem (base + c.val))).val,
      lt_of_lt_of_le (wordOfNat w _).isLt
        (Nat.pow_le_pow_right (by omega) (le_wideWidth input w))⟩
  else
    have hlt_pers :
        packDigits (persCount input) w (fun k => wordOfNat w (x.regs (persReg input k))) <
          2 ^ wideWidth input w :=
      lt_of_lt_of_le (packDigits_lt _ _ _)
        (Nat.pow_le_pow_right (by omega) (persCount_mul_le_wideWidth input w))
    ⟨packDigits (persCount input) w (fun k => wordOfNat w (x.regs (persReg input k))), hlt_pers⟩

theorem dataCellsBounded_packMemWide {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) (x : Data r) :
    DataCellsBounded S w (wideWidth input w) (packMemWide input base S w x) := by
  intro j
  simp [packMemWide, j.isLt]

/-- Unpack `m : Mem (S + 1) (wideWidth input w)` with `argRegs` into `Data r`. -/
@[expose] def unpackDataWide {r : ℕ} (input : Fin r → Bool) (argRegs : Fin r → ℕ) (base S w : ℕ)
    (m : Mem (S + 1) (wideWidth input w)) : Data r where
  regs i :=
    if hi : input i = true then argRegs i
    else
      (unpackDigits (persCount input) w (m (Fin.last S)).val
        (persIdx input i (Bool.eq_false_iff.mpr hi))).val
  mem a :=
    if ha : base ≤ a ∧ a < base + S then
      (m (Fin.castAdd 1 ⟨a - base, by omega⟩)).val % 2 ^ w
    else 0

theorem unpackDataWide_bounded {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + 1) (wideWidth input w)) :
    (unpackDataWide input argRegs base S w m).Bounded w := by
  refine ⟨fun i => ?_, fun a => ?_⟩ <;> dsimp only [unpackDataWide] <;> split_ifs with h
  exacts [harg i h, (unpackDigits _ _ _ _).isLt, Nat.mod_lt _ (Nat.two_pow_pos w), fits_zero w]

theorem unpackDataWide_packMemWide_regs {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} {x : Data r} (hx : x.Bounded w) (i : Fin r) :
    (unpackDataWide input argRegs base S w (packMemWide input base S w x)).regs i =
      if input i then argRegs i else x.regs i := by
  dsimp only [unpackDataWide]
  split_ifs with hi
  · rfl
  · simp [packMemWide, wordOfNat_val_of_lt (hx.1 i)]

theorem unpackDataWide_packMemWide_mem {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} {x : Data r} (hx : x.Bounded w) (a : ℕ) :
    (unpackDataWide input argRegs base S w (packMemWide input base S w x)).mem a =
      (zeroOutside base S x).mem a := by
  dsimp only [unpackDataWide, zeroOutside]
  split_ifs with ha
  · simp [packMemWide, show a - base < S by omega, show base + (a - base) = a by omega,
      Nat.mod_eq_of_lt (hx.2 a), wordOfNat_val_of_lt (hx.2 a)]
  · rfl

/-! #### Finite multi-cell read/write helpers and unified `RegLayout` -/

/-- Read `n` cells `idx 0, …, idx (n - 1)` sequentially in `n` probes without mutating memory. -/
def readFin {cells wCell : ℕ} :
    ∀ {n : ℕ}, (Fin n → Fin cells) → ProbeTree cells wCell (Fin n → Fin (2 ^ wCell))
  | 0, _ => pure Fin.elim0
  | _ + 1, idx => do
      let v₀ ← ProbeTree.read (idx 0)
      let rest ← readFin (fun j => idx j.succ)
      pure (Fin.cons v₀ rest)

@[simp]
theorem run_readFin {cells wCell : ℕ} :
    ∀ {n : ℕ} (idx : Fin n → Fin cells) (m : Mem cells wCell),
      (readFin idx).run m = (fun j => m (idx j), m)
  | 0, _, m => Prod.ext (funext fun j => j.elim0) rfl
  | _ + 1, idx, m => by
    simp only [readFin, ProbeTree.run_bind, ProbeTree.run_read, run_readFin, ProbeTree.run_pure]
    exact Prod.ext (funext fun j => j.cases rfl fun _ => rfl) rfl

@[simp]
theorem probes_readFin {cells wCell : ℕ} :
    ∀ {n : ℕ} (idx : Fin n → Fin cells) (m : Mem cells wCell),
      (readFin idx).probes m = n
  | 0, _, _ => rfl
  | n + 1, idx, m => by
    simp only [readFin, ProbeTree.probes_bind, ProbeTree.probes_read, ProbeTree.run_read,
      probes_readFin, run_readFin, ProbeTree.probes_pure]
    omega

/-- Write `vals 0, …, vals (n - 1)` to `idx 0, …, idx (n - 1)` sequentially in `n` probes. -/
def writeFin {cells wCell : ℕ} :
    ∀ {n : ℕ}, (Fin n → Fin cells) → (Fin n → Fin (2 ^ wCell)) → ProbeTree cells wCell PUnit
  | 0, _, _ => pure PUnit.unit
  | _ + 1, idx, vals => do
      let _ ← ProbeTree.write (idx 0) (vals 0)
      writeFin (fun j => idx j.succ) (fun j => vals j.succ)

@[simp]
theorem probes_writeFin {cells wCell : ℕ} :
    ∀ {n : ℕ} (idx : Fin n → Fin cells) (vals : Fin n → Fin (2 ^ wCell)) (m : Mem cells wCell),
      (writeFin idx vals).probes m = n
  | 0, _, _, _ => rfl
  | n + 1, idx, vals, m => by
    simp only [writeFin, ProbeTree.probes_bind, ProbeTree.probes_write, ProbeTree.run_write,
      probes_writeFin]
    omega

theorem nextMem_writeFin_of_forall_ne {cells wCell : ℕ} :
    ∀ {n : ℕ} (idx : Fin n → Fin cells) (vals : Fin n → Fin (2 ^ wCell))
      (m : Mem cells wCell) (c : Fin cells),
      (∀ j, c ≠ idx j) → ((writeFin idx vals).run m).2 c = m c
  | 0, _, _, _, _, _ => rfl
  | _ + 1, idx, vals, m, c, hne => by
    simp only [writeFin, ProbeTree.run_bind, ProbeTree.run_write]
    rw [nextMem_writeFin_of_forall_ne _ _ _ c (fun j => hne j.succ),
      Function.update_of_ne (hne 0)]

theorem nextMem_writeFin_apply {cells wCell : ℕ} :
    ∀ {n : ℕ} {idx : Fin n → Fin cells}, Function.Injective idx →
      ∀ (vals : Fin n → Fin (2 ^ wCell)) (m : Mem cells wCell) (j : Fin n),
        ((writeFin idx vals).run m).2 (idx j) = vals j
  | 0, _, _, _, _, j => j.elim0
  | n + 1, idx, hinj, vals, m, j => by
    simp only [writeFin, ProbeTree.run_bind, ProbeTree.run_write]
    refine j.cases ?_ (fun i => ?_)
    · rw [nextMem_writeFin_of_forall_ne _ _ _ (idx 0) fun a h => Fin.succ_ne_zero a (hinj h.symm),
        Function.update_self]
    · exact nextMem_writeFin_apply (fun a b h => Fin.succ_injective _ (hinj h))
        (fun a : Fin n => vals a.succ) (Function.update m (idx 0) (vals 0)) i

/-- Unified register/memory layout for Word-RAM-to-cell-probe simulation over `S + regCells` cells
of width `wCell` (`w ≤ wCell`). Instantiated by `standardLayout` (`regCells = persCount input`,
`wCell = w`) and `wideLayout` (`regCells = 1`, `wCell = wideWidth input w`). -/
structure RegLayout (r : ℕ) (input : Fin r → Bool) (base S w regCells wCell : ℕ) where
  /-- Cell width is at least the Word-RAM word width `w`. -/
  hw : w ≤ wCell
  /-- Number of probes used to reload persistent registers at operation entry. -/
  reloadProbes : ℕ
  /-- Number of probes used to spill persistent registers at operation exit. -/
  spillProbes : ℕ
  /-- Reload persistent registers and install caller arguments `argRegs` on `input` registers. -/
  reload : (Fin r → ℕ) → ProbeTree (S + regCells) wCell (Fin r → ℕ)
  /-- Spill persistent registers from final `regs` back to dedicated register cells. -/
  spill : (Fin r → ℕ) → ProbeTree (S + regCells) wCell PUnit
  /-- Pack a Word-RAM `Data r` state into `Mem (S + regCells) wCell`. -/
  pack : Data r → Mem (S + regCells) wCell
  /-- Unpack `Mem (S + regCells) wCell` with `argRegs` into `Data r` (`0` outside `[base, base+S)`).
  -/
  unpack : (Fin r → ℕ) → Mem (S + regCells) wCell → Data r
  /-- Well-formedness of `m` on untouched data/register cells (`True` on `standardLayout`). -/
  ValidMem : Mem (S + regCells) wCell → Prop
  validMem_pack : ∀ (y : Data r), ValidMem (pack y)
  validMem_data : ∀ {m : Mem (S + regCells) wCell}, ValidMem m →
    ∀ idx : Fin S, (m (Fin.castAdd regCells idx)).val < 2 ^ w
  unpack_pers_fits : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) (i : Fin r),
    input i = false → Fits w ((unpack argRegs m).regs i)
  run_reload : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell),
    (reload argRegs).run m = ((unpack argRegs m).regs, m)
  probes_reload : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell),
    (reload argRegs).probes m = reloadProbes
  probes_spill : ∀ (regs : Fin r → ℕ) (m : Mem (S + regCells) wCell),
    (spill regs).probes m = spillProbes
  nextMem_spill_data : ∀ (regs : Fin r → ℕ) (m : Mem (S + regCells) wCell) (idx : Fin S),
    ((spill regs).run m).2 (Fin.castAdd regCells idx) = m (Fin.castAdd regCells idx)
  nextMem_spill_reg : ∀ (y : Data r) (m : Mem (S + regCells) wCell) (c : Fin (S + regCells)),
    (persCount input = 0 → ∀ d : Fin (S + regCells), S ≤ d.val → m d = pack y d) →
    S ≤ c.val → ((spill y.regs).run m).2 c = pack y c
  validMem_reg_zero : ∀ {m : Mem (S + regCells) wCell}, ValidMem m →
    persCount input = 0 → ∀ (y : Data r) (d : Fin (S + regCells)), S ≤ d.val → m d = pack y d
  pack_data : ∀ (y : Data r) (idx : Fin S),
    pack y (Fin.castAdd regCells idx) =
      ⟨(wordOfNat w (y.mem (base + idx.val))).val,
        lt_of_lt_of_le (wordOfNat w _).isLt (Nat.pow_le_pow_right (by omega) hw)⟩
  unpack_mem : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) (a : ℕ),
    (unpack argRegs m).mem a =
      if ha : base ≤ a ∧ a < base + S then
        (m (Fin.castAdd regCells ⟨a - base, by omega⟩)).val % 2 ^ w
      else 0
  unpack_regs_input : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) (i : Fin r),
    input i = true → (unpack argRegs m).regs i = argRegs i
  unpack_regs_pers : ∀ (argRegs₁ argRegs₂ : Fin r → ℕ) (m : Mem (S + regCells) wCell) (i : Fin r),
    input i = false → (unpack argRegs₁ m).regs i = (unpack argRegs₂ m).regs i
  unpack_pack_regs : ∀ (argRegs : Fin r → ℕ) {x : Data r}, x.Bounded w → ∀ i : Fin r,
    (unpack argRegs (pack x)).regs i = if input i then argRegs i else x.regs i

namespace RegLayout

variable {r : ℕ} {input : Fin r → Bool} {base S w regCells wCell : ℕ}

/-- Total reload + spill probe overhead per operation. -/
@[expose] def overhead (L : RegLayout r input base S w regCells wCell) : ℕ :=
  L.reloadProbes + L.spillProbes

theorem unpack_bounded (L : RegLayout r input base S w regCells wCell)
    {argRegs : Fin r → ℕ} (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + regCells) wCell) :
    (L.unpack argRegs m).Bounded w := by
  refine ⟨fun i => ?_, fun a => ?_⟩
  · by_cases hi : input i = true
    · exact L.unpack_regs_input argRegs m i hi ▸ harg i hi
    · exact L.unpack_pers_fits argRegs m i (Bool.eq_false_iff.mpr hi)
  · rw [L.unpack_mem]
    split_ifs
    exacts [Nat.mod_lt _ (Nat.two_pow_pos w), fits_zero w]

theorem unpack_pack_mem (L : RegLayout r input base S w regCells wCell)
    (argRegs : Fin r → ℕ) {x : Data r} (hx : x.Bounded w) (a : ℕ) :
    (L.unpack argRegs (L.pack x)).mem a = (zeroOutside base S x).mem a := by
  rw [L.unpack_mem]
  dsimp only [zeroOutside]
  split_ifs with ha
  · rw [L.pack_data x ⟨a - base, by omega⟩]
    simp [show base + (a - base) = a by omega, Nat.mod_eq_of_lt (hx.2 a),
      wordOfNat_val_of_lt (hx.2 a)]
  · rfl

end RegLayout

/-- Standard `w`-bit cell layout over `S + persCount input` cells (`overhead = 2 * persCount input`,
equal to `0` when `∀ i, input i = true`). -/
def standardLayout {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    RegLayout r input base S w (persCount input) w where
  hw := le_rfl
  reloadProbes := persCount input
  spillProbes := persCount input
  reload argRegs := do
    let vals ← readFin (fun k : Fin (persCount input) => Fin.natAdd S k)
    pure fun i =>
      if hi : input i = true then argRegs i
      else (vals (persIdx input i (Bool.eq_false_iff.mpr hi))).val
  spill regs :=
    writeFin (fun k : Fin (persCount input) => Fin.natAdd S k)
      (fun k => wordOfNat w (regs (persReg input k)))
  pack := packMem input base S w
  unpack argRegs m := unpackData input argRegs base S w m
  ValidMem _ := True
  validMem_pack _ := trivial
  validMem_data {m} _ idx := (m (Fin.castAdd (persCount input) idx)).isLt
  unpack_pers_fits argRegs m i hi := by
    dsimp only [unpackData]
    split_ifs with h
    · exact absurd (hi.symm.trans h) Bool.false_ne_true
    · exact (m _).isLt
  run_reload argRegs m := by
    simp only [ProbeTree.run_bind, run_readFin, ProbeTree.run_pure]
    rfl
  probes_reload argRegs m := by
    simp only [ProbeTree.probes_bind, probes_readFin, run_readFin, ProbeTree.probes_pure, add_zero]
  probes_spill regs m := probes_writeFin _ _ m
  nextMem_spill_data regs m idx :=
    nextMem_writeFin_of_forall_ne _ _ m (Fin.castAdd (persCount input) idx) fun k heq => by
      fin_index
  nextMem_spill_reg y m c _ hc := by
    let k : Fin (persCount input) := ⟨c.val - S, by omega⟩
    have hc_eq : c = Fin.natAdd S k := by fin_index [k]
    have hinj : Function.Injective (fun j : Fin (persCount input) => Fin.natAdd S j) := by
      fin_index
    rw [hc_eq, nextMem_writeFin_apply hinj]
    have hnotlt : ¬ (Fin.natAdd S k).val < S := by simp
    simp only [packMem, hnotlt, ↓reduceDIte]
    have hsub : (⟨(Fin.natAdd S k).val - S, by omega⟩ : Fin (persCount input)) = k := by
      ext; simp
    rw [hsub]
  validMem_reg_zero _ h0 _ d hd := by
    have hlt := d.isLt
    omega
  pack_data y idx := by simp [packMem]
  unpack_mem argRegs m a := by
    dsimp only [unpackData]
    split_ifs with ha
    · exact (Nat.mod_eq_of_lt (m _).isLt).symm
    · rfl
  unpack_regs_input argRegs m i hi := by simp [unpackData, hi]
  unpack_regs_pers _ _ m i hi := by simp [unpackData, hi]
  unpack_pack_regs argRegs {_} hx i := unpackData_packMem_regs hx i

@[simp]
theorem standardLayout_overhead {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (standardLayout input base S w).overhead = 2 * persCount input := by
  simp [RegLayout.overhead, standardLayout, two_mul]

@[simp]
theorem standardLayout_spillProbes {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (standardLayout input base S w).spillProbes = persCount input := by
  simp [standardLayout]

theorem standardLayout_validMem {r : ℕ} (input : Fin r → Bool) (base S w : ℕ)
    (m : Mem (S + persCount input) w) :
    (standardLayout input base S w).ValidMem m := by
  simp [standardLayout]

@[simp]
theorem standardLayout_pack {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (standardLayout input base S w).pack = packMem input base S w := by
  simp [standardLayout]

@[simp]
theorem standardLayout_unpack {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (standardLayout input base S w).unpack =
      fun argRegs m => unpackData input argRegs base S w m := by
  simp [standardLayout]

/-- Wide-cell single-spill layout over `S + 1` cells of width `wideWidth input w` (`0` probes for
reload + spill when `persCount input = 0`, `2` probes when `persCount input > 0`). -/
def wideLayout {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    RegLayout r input base S w 1 (wideWidth input w) where
  hw := le_wideWidth input w
  reloadProbes := if persCount input = 0 then 0 else 1
  spillProbes := if persCount input = 0 then 0 else 1
  reload argRegs :=
    if h0 : persCount input = 0 then
      pure fun i =>
        if hi : input i = true then argRegs i
        else False.elim (by
          have hmem : i ∈ persRegs input := mem_persRegs.mpr (Bool.eq_false_iff.mpr hi)
          have hpos : 0 < persCount input := Finset.card_pos.mpr ⟨i, hmem⟩
          omega)
    else do
      let cellVal ← ProbeTree.read (Fin.last S)
      pure fun i =>
        if hi : input i = true then argRegs i
        else
          (unpackDigits (persCount input) w cellVal.val
            (persIdx input i (Bool.eq_false_iff.mpr hi))).val
  spill regs :=
    if h0 : persCount input = 0 then
      pure PUnit.unit
    else
      have hlt_pers :
          packDigits (persCount input) w (fun k => wordOfNat w (regs (persReg input k))) <
            2 ^ wideWidth input w :=
        lt_of_lt_of_le (packDigits_lt _ _ _)
          (Nat.pow_le_pow_right (by omega) (persCount_mul_le_wideWidth input w))
      ProbeTree.write (Fin.last S)
        ⟨packDigits (persCount input) w (fun k => wordOfNat w (regs (persReg input k))), hlt_pers⟩
  pack := packMemWide input base S w
  unpack argRegs m := unpackDataWide input argRegs base S w m
  ValidMem m := DataCellsBounded S w (wideWidth input w) m ∧
    (persCount input = 0 → (m (Fin.last S)).val = 0)
  validMem_pack y := ⟨dataCellsBounded_packMemWide input base S w y, fun h0 => by
    simp [packMemWide, packDigits_eq_zero_of_zero h0]⟩
  validMem_data hm := hm.1
  unpack_pers_fits argRegs m i hi := by
    dsimp only [unpackDataWide]
    split_ifs with h
    · exact absurd (hi.symm.trans h) Bool.false_ne_true
    · exact (unpackDigits _ _ _ _).isLt
  run_reload argRegs m := by
    by_cases h0 : persCount input = 0
    · simp only [h0, ↓reduceDIte, ProbeTree.run_pure]
      refine Prod.ext (funext fun i => ?_) rfl
      dsimp only [unpackDataWide]
      split_ifs with hi
      · rfl
      · exfalso
        have hmem : i ∈ persRegs input := mem_persRegs.mpr (Bool.eq_false_iff.mpr hi)
        have hpos : 0 < persCount input := Finset.card_pos.mpr ⟨i, hmem⟩
        omega
    · simp only [h0, ↓reduceDIte, ProbeTree.run_bind, ProbeTree.run_read, ProbeTree.run_pure]
      rfl
  probes_reload argRegs m := by
    by_cases h0 : persCount input = 0 <;> simp [h0]
  probes_spill regs m := by
    by_cases h0 : persCount input = 0 <;> simp [h0]
  nextMem_spill_data regs m idx := by
    by_cases h0 : persCount input = 0
    · simp [h0]
    · simp only [h0, ↓reduceDIte, ProbeTree.run_write]
      have hne : Fin.castAdd 1 idx ≠ Fin.last S := by fin_index
      exact Function.update_of_ne hne _ m
  nextMem_spill_reg y m c hzero hc := by
    have hc_eq : c = Fin.last S := by fin_index
    subst hc_eq
    by_cases h0 : persCount input = 0
    · simp only [h0, ↓reduceDIte, ProbeTree.run_pure]
      exact hzero h0 (Fin.last S) hc
    · simp [h0, packMemWide]
  validMem_reg_zero hm h0 y d hd := by
    have hd_eq : d = Fin.last S := by fin_index
    subst hd_eq
    refine Fin.ext ?_
    simp [hm.2 h0, packMemWide, packDigits_eq_zero_of_zero h0]
  pack_data y idx := by simp [packMemWide]
  unpack_mem _ _ _ := rfl
  unpack_regs_input argRegs m i hi := by simp [unpackDataWide, hi]
  unpack_regs_pers _ _ m i hi := by simp [unpackDataWide, hi]
  unpack_pack_regs argRegs {_} hx i := unpackDataWide_packMemWide_regs hx i

@[simp]
theorem wideLayout_overhead {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (wideLayout input base S w).overhead = if persCount input = 0 then 0 else 2 := by
  by_cases h0 : persCount input = 0 <;> simp [RegLayout.overhead, wideLayout, h0]

theorem wideLayout_overhead_le {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (wideLayout input base S w).overhead ≤ 2 := by
  rw [wideLayout_overhead]
  split_ifs <;> omega

@[simp]
theorem wideLayout_pack {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (wideLayout input base S w).pack = packMemWide input base S w := by
  simp [wideLayout]

@[simp]
theorem wideLayout_unpack {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (wideLayout input base S w).unpack =
      fun argRegs m => unpackDataWide input argRegs base S w m := by
  simp [wideLayout]

@[simp]
theorem wideLayout_validMem_iff {r : ℕ} (input : Fin r → Bool) (base S w : ℕ)
    (m : Mem (S + 1) (wideWidth input w)) :
    (wideLayout input base S w).ValidMem m ↔
      DataCellsBounded S w (wideWidth input w) m ∧
        (persCount input = 0 → (m (Fin.last S)).val = 0) := by
  simp [wideLayout]


/-! ### 3. Intra-operation write buffer and deterministic `ProbeTree` simulation -/

/-- Intra-operation simulator configuration over `[base, base + S)` with pure-Lean write buffer
`writeBuf` and outside-footprint memory `extMem`. -/
inductive SimOutcome (S w r : ℕ) : Type where
  | running (pc : ℕ) (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) (extMem : ℕ → ℕ)
  | halted (out : ℕ) (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) (extMem : ℕ → ℕ)
  | faulted

/-- Number of modified cells buffered in `writeBuf`. -/
def dirtyCount {S w : ℕ} (writeBuf : Fin S → Option (Fin (2 ^ w))) : ℕ :=
  (Finset.univ.filter fun idx : Fin S => (writeBuf idx).isSome).card

private theorem dirtyCount_empty (S w : ℕ) :
    dirtyCount (fun _ : Fin S => (none : Option (Fin (2 ^ w)))) = 0 := by
  simp [dirtyCount]

private theorem dirtyCount_update_le {S w : ℕ} (writeBuf : Fin S → Option (Fin (2 ^ w)))
    (idx : Fin S) (v : Fin (2 ^ w)) :
    dirtyCount (Function.update writeBuf idx (some v)) ≤ dirtyCount writeBuf + 1 := by
  refine (Finset.card_le_card (t := insert idx (Finset.univ.filter fun j => (writeBuf j).isSome))
    fun j hj => ?_).trans (Finset.card_insert_le _ _)
  by_cases hji : j = idx <;> simp_all [Function.update_of_ne]

/-- Reconstruct the full Word-RAM `Data r` represented by `(regs, writeBuf, extMem)` over base
memory `m`. -/
def reconstructData {r S regCells w wCell : ℕ} (base : ℕ) (m : Mem (S + regCells) wCell)
    (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) (extMem : ℕ → ℕ) : Data r where
  regs := regs
  mem a :=
    if ha : base ≤ a ∧ a < base + S then
      match writeBuf ⟨a - base, by omega⟩ with
      | some v => v.val
      | none => (m (Fin.castAdd regCells ⟨a - base, by omega⟩)).val % 2 ^ w
    else extMem a

private theorem reconstructData_init {r : ℕ} {input : Fin r → Bool}
    {base S w regCells wCell : ℕ} (L : RegLayout r input base S w regCells wCell)
    (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) :
    reconstructData (w := w) base m (L.unpack argRegs m).regs (fun _ => none) (fun _ => 0) =
      L.unpack argRegs m :=
  Data.ext rfl (funext fun a => (L.unpack_mem argRegs m a).symm)

/-- Buffering a store inside `[base, base + S)` is a memory write on the reconstructed data. -/
private theorem reconstructData_update_buf {r S regCells w wCell : ℕ} (base : ℕ)
    (m : Mem (S + regCells) wCell) (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w)))
    (extMem : ℕ → ℕ) {a v : ℕ} (ha : base ≤ a ∧ a < base + S) (hv : Fits w v) :
    reconstructData base m regs
        (Function.update writeBuf ⟨a - base, by omega⟩ (some (wordOfNat w v))) extMem =
      (reconstructData base m regs writeBuf extMem).write a v := by
  refine Data.ext rfl (funext fun b => ?_)
  rcases eq_or_ne b a with rfl | hb
  · simp [reconstructData, Data.write, ha, wordOfNat_val_of_lt hv]
  · dsimp only [reconstructData, Data.write]
    rw [Function.update_of_ne hb]
    split_ifs with hba
    · rw [Function.update_of_ne (by fin_index)]
    · rfl

/-- A store outside `[base, base + S)` is a memory write on the reconstructed data. -/
private theorem reconstructData_update_ext {r S regCells w wCell : ℕ} (base : ℕ)
    (m : Mem (S + regCells) wCell) (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w)))
    (extMem : ℕ → ℕ) {a : ℕ} (v : ℕ) (ha : ¬(base ≤ a ∧ a < base + S)) :
    reconstructData base m regs writeBuf (Function.update extMem a v) =
      (reconstructData base m regs writeBuf extMem).write a v := by
  refine Data.ext rfl (funext fun b => ?_)
  simp only [reconstructData, Data.write, Function.update_apply]
  split_ifs with h hb <;> first | rfl | exact absurd (hb ▸ h) ha

/-- Embed a `w`-bit word into `Fin (2 ^ wCell)` when `w ≤ wCell`. -/
def liftCellWord {w wCell : ℕ} (hw : w ≤ wCell) (v : Fin (2 ^ w)) : Fin (2 ^ wCell) :=
  ⟨v.val, lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) hw)⟩

/-- Flush modified cells from `writeBuf` (`0 .. j - 1`) to data cells `0 .. S - 1`. -/
def flushAux {S regCells w wCell : ℕ} (hw : w ≤ wCell)
    (writeBuf : Fin S → Option (Fin (2 ^ w))) :
    (j : ℕ) → j ≤ S → ProbeTree (S + regCells) wCell PUnit
  | 0, _ => pure PUnit.unit
  | k + 1, hk => do
      let _ ← flushAux hw writeBuf k (by omega)
      let idx : Fin S := ⟨k, hk⟩
      match writeBuf idx with
      | none => pure PUnit.unit
      | some v => ProbeTree.write (Fin.castAdd regCells idx) (liftCellWord hw v)

/-- Flush all modified cells of `writeBuf` to `Mem (S + regCells) wCell` in `dirtyCount writeBuf`
write probes. -/
def flushWriteBuf {S regCells w wCell : ℕ} (hw : w ≤ wCell)
    (writeBuf : Fin S → Option (Fin (2 ^ w))) : ProbeTree (S + regCells) wCell PUnit :=
  flushAux hw writeBuf S le_rfl

private theorem flushAux_spec {S regCells w wCell : ℕ} (hw : w ≤ wCell)
    (writeBuf : Fin S → Option (Fin (2 ^ w))) :
    ∀ (j : ℕ) (hj : j ≤ S) (m : Mem (S + regCells) wCell),
      (flushAux hw writeBuf j hj).probes m =
        (∑ i ∈ Finset.range j, if h : i < S then (if (writeBuf ⟨i, h⟩).isSome then 1 else 0)
          else 0) ∧
      (∀ idx : Fin S, idx.val < j →
        ((flushAux hw writeBuf j hj).run m).2 (Fin.castAdd regCells idx) =
          match writeBuf idx with
          | some v => liftCellWord hw v
          | none => m (Fin.castAdd regCells idx)) ∧
      (∀ c : Fin (S + regCells), j ≤ c.val →
        ((flushAux hw writeBuf j hj).run m).2 c = m c)
  | 0, _, m => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | k + 1, hk, m => by
    obtain ⟨hpr, hlt, hge⟩ := flushAux_spec hw writeBuf k (by omega) m
    have hsplit : ∀ idx : Fin S, idx.val < k + 1 → idx.val < k ∨ idx = ⟨k, hk⟩ := fun idx h =>
      (Nat.lt_succ_iff_lt_or_eq.mp h).imp_right Fin.ext
    simp only [Finset.sum_range_succ, ← hpr, show k < S from hk, ↓reduceDIte, flushAux]
    cases hwb : writeBuf ⟨k, hk⟩ with
    | none =>
      simp only [ProbeTree.probes_bind, ProbeTree.probes_pure, ProbeTree.run_bind,
        ProbeTree.run_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, true_and]
      refine ⟨fun idx hidx => ?_, fun c hc => hge c (by omega)⟩
      obtain hlt_k | rfl := hsplit idx hidx
      · exact hlt idx hlt_k
      · exact hwb ▸ hge (Fin.castAdd regCells ⟨k, hk⟩) le_rfl
    | some v =>
      simp only [ProbeTree.probes_bind, ProbeTree.probes_write, ProbeTree.run_bind,
        ProbeTree.run_write, Option.isSome_some, ↓reduceIte, true_and]
      refine ⟨fun idx hidx => ?_, fun c hc => ?_⟩
      · obtain hlt_k | rfl := hsplit idx hidx
        · rw [Function.update_of_ne (by fin_index), hlt idx hlt_k]
        · rw [hwb, Function.update_self]
      · rw [Function.update_of_ne (by fin_index), hge c (by omega)]

theorem probes_flushWriteBuf {S regCells w wCell : ℕ} (hw : w ≤ wCell)
    (writeBuf : Fin S → Option (Fin (2 ^ w))) (m : Mem (S + regCells) wCell) :
    (flushWriteBuf hw writeBuf).probes m = dirtyCount writeBuf := by
  rw [flushWriteBuf, (flushAux_spec hw writeBuf S le_rfl m).1, dirtyCount, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => dite_eq_left i.isLt

/-- Flush `writeBuf` and spill persistent registers according to `L`, producing `L.pack y` whenever
`y = reconstructData base m regs writeBuf extMem` and `y.Bounded w` and `L.ValidMem m`. -/
def commitHalted {r : ℕ} {input : Fin r → Bool} {base S w regCells wCell : ℕ}
    (L : RegLayout r input base S w regCells wCell)
    (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) :
    ProbeTree (S + regCells) wCell PUnit := do
  let _ ← flushWriteBuf L.hw writeBuf
  L.spill regs

theorem commitHalted_spec {r : ℕ} {input : Fin r → Bool} {base S w regCells wCell : ℕ}
    (L : RegLayout r input base S w regCells wCell)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) (extMem : ℕ → ℕ) :
    ((commitHalted L regs writeBuf).run m).2 =
        L.pack (reconstructData base m regs writeBuf extMem) ∧
      (commitHalted L regs writeBuf).probes m = dirtyCount writeBuf + L.spillProbes := by
  set y := reconstructData base m regs writeBuf extMem
  obtain ⟨-, hlt_f, hge_f⟩ := flushAux_spec L.hw writeBuf S le_rfl m
  refine ⟨funext fun c => ?_, by
    simp only [commitHalted, ProbeTree.probes_bind, probes_flushWriteBuf, L.probes_spill]⟩
  simp only [commitHalted, ProbeTree.run_bind, flushWriteBuf]
  by_cases hc : c.val < S
  · obtain ⟨idx, rfl⟩ : ∃ idx : Fin S, c = Fin.castAdd regCells idx := ⟨⟨c.val, hc⟩, rfl⟩
    have hlt_m := L.validMem_data hm idx
    cases hwb : writeBuf idx <;>
      · rw [L.nextMem_spill_data, L.pack_data y idx, hlt_f idx hc]
        simp only [y, reconstructData, Nat.le_add_right, Nat.add_lt_add_iff_left, idx.isLt,
          and_self, ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta, hwb]
        simp [liftCellWord, Nat.mod_eq_of_lt hlt_m, wordOfNat_val_of_lt hlt_m]
  · exact L.nextMem_spill_reg y _ c
      (fun h0 d hd => (hge_f d hd).trans (L.validMem_reg_zero hm h0 y d hd)) (Nat.le_of_not_lt hc)

/-! #### Single-step and clocked deterministic `ProbeTree` simulation -/

/-- One step of buffered deterministic flat-program simulation in `ProbeTree` (issuing `1` read
probe on an uncached `.load` inside `[base, base + S)` and `0` probes on all other instructions). -/
def simStepDet {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r) :
    SimOutcome S w r → ProbeTree (S + regCells) wCell (SimOutcome S w r)
  | .halted out regs wb ext => pure (.halted out regs wb ext)
  | .faulted => pure .faulted
  | .running pc regs writeBuf extMem =>
    match p[pc]? with
    | none => pure .faulted
    | some (.halt i) => pure (.halted (regs i) regs writeBuf extMem)
    | some (.jump t) => pure (.running t regs writeBuf extMem)
    | some (.branch c t) =>
      pure (.running (if c.Holds ⟨regs, fun _ => 0⟩ then t else pc + 1) regs writeBuf extMem)
    | some (.rand _ _) => pure .faulted
    | some (.op (.const d v)) =>
      if Fits w v then
        pure (.running (pc + 1) (Function.update regs d v) writeBuf extMem)
      else
        pure .faulted
    | some (.op (.copy d src)) =>
      pure (.running (pc + 1) (Function.update regs d (regs src)) writeBuf extMem)
    | some (.op (.alu f d args)) =>
      match B.interp w f (regs ∘ args) with
      | some v =>
        if Fits w v then
          pure (.running (pc + 1) (Function.update regs d v) writeBuf extMem)
        else
          pure .faulted
      | none => pure .faulted
    | some (.op (.load d a)) =>
      let addr := regs a
      if ha : base ≤ addr ∧ addr < base + S then
        let idx : Fin S := ⟨addr - base, by omega⟩
        match writeBuf idx with
        | some v =>
          pure (.running (pc + 1) (Function.update regs d v.val) writeBuf extMem)
        | none => do
          let raw ← ProbeTree.read (Fin.castAdd regCells idx)
          pure (.running (pc + 1) (Function.update regs d (raw.val % 2 ^ w)) writeBuf extMem)
      else
        pure (.running (pc + 1) (Function.update regs d (extMem addr)) writeBuf extMem)
    | some (.op (.store a src)) =>
      let addr := regs a
      let val := regs src
      if ha : base ≤ addr ∧ addr < base + S then
        pure (.running (pc + 1) regs
          (Function.update writeBuf ⟨addr - base, by omega⟩ (some (wordOfNat w val))) extMem)
      else
        pure (.running (pc + 1) regs writeBuf (Function.update extMem addr val))

private theorem cond_holds_regs_only {r : ℕ} (c : Cond r) (x : Data r) :
    c.Holds ⟨x.regs, fun _ => 0⟩ ↔ c.Holds x := by
  cases c <;> rfl

/-- A `simStepDet` step leaves cell memory untouched and issues at most one probe. -/
private theorem simStepDet_nextMem_probes {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (st : SimOutcome S w r) (m : Mem (S + regCells) wCell) :
    ((simStepDet (regCells := regCells) (wCell := wCell) base p st).run m).2 = m ∧
      (simStepDet (regCells := regCells) (wCell := wCell) base p st).probes m ≤ 1 := by
  cases st with
  | running pc regs writeBuf extMem =>
    dsimp only [simStepDet]
    repeat' split
    all_goals simp
  | _ => exact ⟨rfl, Nat.zero_le 1⟩

theorem simStepDet_nextMem {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r)
    (st : SimOutcome S w r) (m : Mem (S + regCells) wCell) :
    ((simStepDet (regCells := regCells) (wCell := wCell) base p st).run m).2 = m :=
  (simStepDet_nextMem_probes base p st m).1

/-- Exact single-step correspondence between `simStepDet` and `WordRAM.step`. -/
theorem simStepDet_spec {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r)
    (pc : ℕ) {regs : Fin r → ℕ} {writeBuf : Fin S → Option (Fin (2 ^ w))} {extMem : ℕ → ℕ}
    (m : Mem (S + regCells) wCell)
    (hx : (reconstructData base m regs writeBuf extMem).Bounded w) :
    let x := reconstructData base m regs writeBuf extMem
    let t := simStepDet (regCells := regCells) (w := w) (wCell := wCell)
      base p (.running pc regs writeBuf extMem)
    (t.run m).2 = m ∧
    match step w p ⟨pc, x⟩ with
    | .next s' =>
      ∃ writeBuf' extMem',
        (t.run m).1 = .running s'.pc s'.data.regs writeBuf' extMem' ∧
        reconstructData base m s'.data.regs writeBuf' extMem' = s'.data ∧
        t.probes m + dirtyCount writeBuf' ≤ 1 + dirtyCount writeBuf
    | .halt v =>
      (t.run m).1 = .halted v regs writeBuf extMem ∧ t.probes m = 0
    | .fault =>
      (t.run m).1 = .faulted ∧ t.probes m = 0 := by
  intro x t
  refine ⟨simStepDet_nextMem base p _ m, ?_⟩
  dsimp only [t, simStepDet, step]
  rcases hp : p[pc]? with _ | (o | tgt | ⟨c, tgt⟩ | i | _)
  · simp
  · cases o with dsimp only
    | const d v =>
      by_cases hv : Fits w v
      · simp only [Op.eval_const, Data.put_of_fits hv, hv, ↓reduceIte]
        exact ⟨writeBuf, extMem, rfl, rfl, by simp⟩
      · simp [Data.put, hv]
    | copy d src => exact ⟨writeBuf, extMem, rfl, rfl, by simp⟩
    | alu f d args =>
      rw [Op.eval_alu, show x.regs ∘ args = regs ∘ args from rfl]
      cases hbi : B.interp w f (regs ∘ args) with
      | none => simp
      | some v =>
        by_cases hv : Fits w v
        · simp only [Option.bind_some, Data.put_of_fits hv, hv, ↓reduceIte]
          exact ⟨writeBuf, extMem, rfl, rfl, by simp⟩
        · simp [Data.put, hv]
    | load d a =>
      -- In each sub-case the loaded value is `x.mem (regs a)` by definition of `reconstructData`.
      refine ⟨writeBuf, extMem, ?_, rfl, ?_⟩
      · dsimp only [Op.eval_load, x, reconstructData]
        split_ifs with ha <;> [cases writeBuf ⟨regs a - base, by omega⟩ <;> rfl; rfl]
      · split_ifs with ha <;> [cases writeBuf ⟨regs a - base, by omega⟩ <;> simp; simp]
    | store a src =>
      dsimp only [Op.eval_store]
      split_ifs with ha
      · exact ⟨_, extMem, rfl, reconstructData_update_buf base m regs writeBuf extMem ha (hx.1 src),
          by simpa [add_comm] using dirtyCount_update_le writeBuf _ _⟩
      · exact ⟨writeBuf, _, rfl, reconstructData_update_ext base m regs writeBuf extMem _ ha,
          by simp⟩
  · exact ⟨writeBuf, extMem, rfl, rfl, by simp⟩
  · exact ⟨writeBuf, extMem, congrArg (SimOutcome.running · regs writeBuf extMem)
      (if_congr (cond_holds_regs_only c x) rfl rfl), rfl, by simp⟩
  · simp [x, reconstructData]
  · simp

/-- Run `simStepDet` for `K` clocked steps. -/
def simLoopDet {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r) :
    ℕ → SimOutcome S w r → ProbeTree (S + regCells) wCell (SimOutcome S w r)
  | 0, st => pure st
  | K + 1, st => do
      let st' ← simStepDet base p st
      simLoopDet base p K st'

private theorem simLoopDet_halted {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (K : ℕ) (out : ℕ) (regs : Fin r → ℕ)
    (wb : Fin S → Option (Fin (2 ^ w))) (ext : ℕ → ℕ) (m : Mem (S + regCells) wCell) :
    (simLoopDet (regCells := regCells) (wCell := wCell) base p K (.halted out regs wb ext)).run m =
      (.halted out regs wb ext, m) ∧
    (simLoopDet (regCells := regCells) (wCell := wCell) base p K (.halted out regs wb ext)).probes m
      = 0 := by
  induction K with
  | zero => exact ⟨rfl, rfl⟩
  | succ K ih => exact ih

/-- A halting run of `n` continuing steps is reproduced by `simLoopDet` with any fuel `K ≥ n + 1`,
by induction on the fuel: each `simStepDet` either takes the next step of the run or halts. -/
private theorem simLoopDet_of_runs_halt {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) {s t : State r} {n v K : ℕ}
    (hruns : Runs w p s t n) (hhalt : step w p t = .halt v) (hK : n + 1 ≤ K)
    {wb : Fin S → Option (Fin (2 ^ w))} {ext : ℕ → ℕ}
    (m : Mem (S + regCells) wCell)
    (hrec : reconstructData base m s.data.regs wb ext = s.data)
    (hs_bdd : s.data.Bounded w) :
    ∃ wb' ext',
      (simLoopDet (regCells := regCells) (wCell := wCell)
        base p K (.running s.pc s.data.regs wb ext)).run m =
          (.halted v t.data.regs wb' ext', m) ∧
      reconstructData base m t.data.regs wb' ext' = t.data ∧
      (simLoopDet (regCells := regCells) (wCell := wCell)
        base p K (.running s.pc s.data.regs wb ext)).probes m + dirtyCount wb' ≤
          n + dirtyCount wb := by
  induction K generalizing s n wb ext with
  | zero => omega
  | succ K ih =>
    have hspec := simStepDet_spec (regCells := regCells) (wCell := wCell) base p s.pc m
      (hrec ▸ hs_bdd)
    dsimp only at hspec
    rw [hrec] at hspec
    rcases n with _ | n
    · obtain rfl := hruns.zero
      rw [hhalt] at hspec
      obtain ⟨hm_eq, hrun1, hpr1⟩ := hspec
      obtain ⟨hrem_run, hrem_pr⟩ := simLoopDet_halted (regCells := regCells) (wCell := wCell)
        base p K v s.data.regs wb ext m
      exact ⟨wb, ext, by simp only [simLoopDet, ProbeTree.run_bind, hrun1, hm_eq, hrem_run], hrec,
        by simp only [simLoopDet, ProbeTree.probes_bind, hpr1, hrun1, hm_eq, hrem_pr]; omega⟩
    · obtain ⟨u, hstep, hrest⟩ := hruns.succ'
      rw [show step w p s = .next u from hstep] at hspec
      obtain ⟨hm_eq, wb₁, ext₁, hrun1, hrec₁, hpr1⟩ := hspec
      obtain ⟨wb', ext', hrun, hrec', hpr⟩ := ih hrest (by omega) hrec₁ (hstep.bounded hs_bdd)
      exact ⟨wb', ext', by simp only [simLoopDet, ProbeTree.run_bind, hrun1, hm_eq, hrun], hrec',
        by simp only [simLoopDet, ProbeTree.probes_bind, hrun1, hm_eq]; omega⟩

theorem nextMem_writeFin_id {cells wCell : ℕ} (vals m : Mem cells wCell) :
    ((writeFin (fun i : Fin cells => i) vals).run m).2 = vals := by
  funext j
  exact nextMem_writeFin_apply (fun _ _ h => h) vals m j

/-! #### Deterministic flat-program and structured `ExecWithin` entrypoints -/

/-- Clocked deterministic `ProbeTree` simulator for a flat `WordRAM.Program B r`: reloads
persistent registers according to `L`, runs `K` buffered steps of `p` from `pc = 0`, and on clean
halt flushes modified data cells and spills persistent registers. -/
def simProgDet {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ) :
    ProbeTree (S + regCells) wCell Out := do
  let regs₀ ← L.reload argRegs
  let out ← simLoopDet base p K (.running 0 regs₀ (fun _ => none) (fun _ => 0))
  match out with
  | .halted v regs' writeBuf' _ =>
    let _ ← commitHalted L regs' writeBuf'
    pure ((decode v regs').getD defaultAns)
  | _ => pure defaultAns

/-- Any halting run of `p` from `⟨0, L.unpack argRegs m⟩` with `n` continuing steps (`n + 1 ≤ K`)
is simulated identically by `simProgDet` in at most `n + L.overhead` cell probes, leaving
`L.pack t.data` in memory. -/
theorem simProgDet_spec {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {t : State r} {n v K : ℕ}
    (hruns : Runs w p ⟨0, L.unpack argRegs m⟩ t n)
    (hhalt : step w p t = .halt v) (hK : n + 1 ≤ K) :
    (simProgDet L p argRegs decode defaultAns K).run m =
        ((decode v t.data.regs).getD defaultAns, L.pack t.data) ∧
      (simProgDet L p argRegs decode defaultAns K).probes m ≤ n + L.overhead := by
  obtain ⟨wb', ext', hloop_run, hrec', hloop_pr⟩ :=
    simLoopDet_of_runs_halt (regCells := regCells) (wCell := wCell) base p hruns hhalt hK m
      (reconstructData_init L argRegs m) (L.unpack_bounded harg m)
  obtain ⟨hcommit_mem, hcommit_pr⟩ := commitHalted_spec L hm t.data.regs wb' ext'
  rw [hrec'] at hcommit_mem
  simp only [dirtyCount_empty] at hloop_pr
  refine ⟨by simp only [simProgDet, ProbeTree.run_bind, L.run_reload, hloop_run,
    ProbeTree.run_pure, hcommit_mem], ?_⟩
  simp only [simProgDet, ProbeTree.probes_bind, L.probes_reload, L.run_reload, hloop_run,
    hcommit_pr, ProbeTree.probes_pure, add_zero, RegLayout.overhead]
  omega

/-- Clocked deterministic `ProbeTree` initializer simulator: starts from externally supplied
initial registers `initRegs` (`0` reload probes), runs `K` buffered steps of `p` on zeroed cell
memory, and on clean halt flushes modified data cells and spills persistent registers in
`L.spillProbes` probes. -/
def simProgInitDet {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (initRegs : Fin r → ℕ) (K : ℕ) :
    ProbeTree (S + regCells) wCell PUnit := do
  let out ← simLoopDet base p K (.running 0 initRegs (fun _ => none) (fun _ => 0))
  match out with
  | .halted _ regs' writeBuf' _ => commitHalted L regs' writeBuf'
  | _ => pure PUnit.unit

/-- Starting from zeroed cell memory `fun _ => 0` (when `hm₀ : L.ValidMem (fun _ => 0)`), any
halting run of `p` from `⟨0, { regs := initRegs, mem := fun _ => 0 }⟩` in `n` continuing steps
(`n + 1 ≤ K`) is simulated by `simProgInitDet` in at most `n + L.spillProbes` cell probes, leaving
`L.pack t.data` in memory. -/
theorem simProgInitDet_spec {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (initRegs : Fin r → ℕ)
    (hm₀ : L.ValidMem (fun _ => 0))
    (hregs : ∀ i, Fits w (initRegs i))
    {t : State r} {n v K : ℕ}
    (hruns : Runs w p ⟨0, { regs := initRegs, mem := fun _ => 0 }⟩ t n)
    (hhalt : step w p t = .halt v) (hK : n + 1 ≤ K) :
    (simProgInitDet L p initRegs K).run (fun _ => 0) = (PUnit.unit, L.pack t.data) ∧
      (simProgInitDet L p initRegs K).probes (fun _ => 0) ≤ n + L.spillProbes := by
  obtain ⟨wb', ext', hloop_run, hrec', hloop_pr⟩ :=
    simLoopDet_of_runs_halt (regCells := regCells) (wCell := wCell) (wb := fun _ => none)
      (ext := fun _ => 0) base p hruns hhalt hK (fun _ => 0)
      (Data.ext rfl (funext fun a => by simp [reconstructData])) ⟨hregs, fun _ => fits_zero w⟩
  obtain ⟨hcommit_mem, hcommit_pr⟩ := commitHalted_spec L hm₀ t.data.regs wb' ext'
  rw [hrec'] at hcommit_mem
  simp only [dirtyCount_empty] at hloop_pr
  constructor
  · simp only [simProgInitDet, ProbeTree.run_bind, hloop_run]
    exact Prod.ext rfl hcommit_mem
  · simp only [simProgInitDet, ProbeTree.probes_bind, hloop_run, hcommit_pr]
    omega

/-- Exact halting step count of `p` from `⟨0, L.unpack argRegs m⟩` when a halting run exists, or
`0` otherwise. -/
noncomputable def haltFuel {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) : ℕ :=
  letI := Classical.propDecidable
  if h : ∃ n, ∃ v, Executes w p ⟨0, L.unpack argRegs m⟩ v n then Classical.choose h else 0

/-- Uniform fuel across all `m : Mem (S + regCells) wCell` on which `p` halts. -/
noncomputable def autoFuel {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ) : ℕ :=
  Finset.univ.sup (haltFuel L p argRegs)

theorem le_autoFuel_of_runs_halt {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    {p : Program B r} {argRegs : Fin r → ℕ} {m : Mem (S + regCells) wCell}
    {t : State r} {n v : ℕ}
    (hruns : Runs w p ⟨0, L.unpack argRegs m⟩ t n) (hhalt : step w p t = .halt v) :
    n + 1 ≤ autoFuel L p argRegs := by
  have hex : Executes w p ⟨0, L.unpack argRegs m⟩ v (n + 1) := ⟨t, n, hruns, hhalt, rfl⟩
  have hmem : ∃ n', ∃ v', Executes w p ⟨0, L.unpack argRegs m⟩ v' n' := ⟨n + 1, v, hex⟩
  refine le_of_eq_of_le ?_ (Finset.le_sup (f := haltFuel L p argRegs) (Finset.mem_univ m))
  simp only [haltFuel, hmem, ↓reduceDIte]
  exact ((Classical.choose_spec hmem).choose_spec.unique hex).2.symm

/-- Automatic-fuel deterministic `ProbeTree` simulator: chooses fuel uniformly over the finite
memory space `Mem (S + regCells) wCell` so callers need not supply an external step bound `K`. -/
noncomputable def simProgDetAuto {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) :
    ProbeTree (S + regCells) wCell Out :=
  simProgDet L p argRegs decode defaultAns (autoFuel L p argRegs)

/-- Automatic-fuel simulation of any deterministic halting run of `p` in `≤ n + L.overhead` cell
probes (`≤ T_flat - 1 + L.overhead` when `Executes w p ⟨0, x₀⟩ v T_flat`). -/
theorem simProgDetAuto_spec {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {t : State r} {n v : ℕ}
    (hruns : Runs w p ⟨0, L.unpack argRegs m⟩ t n)
    (hhalt : step w p t = .halt v) :
    (simProgDetAuto L p argRegs decode defaultAns).run m =
        ((decode v t.data.regs).getD defaultAns, L.pack t.data) ∧
      (simProgDetAuto L p argRegs decode defaultAns).probes m ≤ n + L.overhead :=
  simProgDet_spec L p argRegs decode defaultAns hm harg hruns hhalt
    (le_autoFuel_of_runs_halt L hruns hhalt)

private theorem simExecWithinLayout {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m) {y : Data r} {T : ℕ}
    (hexec : ExecWithin w c (L.unpack argRegs m) y T) :
    let tree := simProgDetAuto L (c.program retReg) argRegs (fun _ regs => decode regs) defaultAns
    tree.run m = ((decode y.regs).getD defaultAns, L.pack y) ∧
      tree.probes m ≤ T + L.overhead := by
  obtain ⟨n, hn_le, hex⟩ := hexec
  exact (simProgDetAuto_spec L (c.program retReg) argRegs (fun _ regs => decode regs) defaultAns
    hm harg (hex.runs (pc := 0) (p := c.program retReg) (Program.Contains.self _).append_left)
    (step_halt (i := retReg) (by simp [Code.program]))).imp_right
      (·.trans (Nat.add_le_add_right hn_le _))

/-- Structured `ExecWithin` simulation in standard `w`-bit layout (`S + persCount input` cells of
width `w`): simulates `c` in at most `T + 2 * persCount input` probes (`≤ T` when
`persCount input = 0`). -/
theorem simExecWithin {B : Basis} {r S w : ℕ} {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + persCount input) w) {y : Data r} {T : ℕ}
    (hexec : ExecWithin w c (unpackData input argRegs base S w m) y T) :
    let tree := simProgDetAuto (standardLayout input base S w) (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns
    tree.run m = ((decode y.regs).getD defaultAns, packMem input base S w y) ∧
      tree.probes m ≤ T + 2 * persCount input :=
  standardLayout_overhead input base S w ▸ simExecWithinLayout (standardLayout input base S w)
    c retReg argRegs decode defaultAns harg trivial hexec

/-- Structured `ExecWithin` simulation in wide-cell single-spill layout (`S + 1` cells of width
`wideWidth input w`): simulates `c` in at most `T + (if persCount input = 0 then 0 else 2)` probes
(`≤ T + 2` regardless of `r`). -/
theorem simExecWithinWide {B : Basis} {r S w : ℕ} {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {m : Mem (S + 1) (wideWidth input w)}
    (hm : (wideLayout input base S w).ValidMem m) {y : Data r} {T : ℕ}
    (hexec : ExecWithin w c (unpackDataWide input argRegs base S w m) y T) :
    let tree := simProgDetAuto (wideLayout input base S w) (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns
    tree.run m = ((decode y.regs).getD defaultAns, packMemWide input base S w y) ∧
      tree.probes m ≤ T + (if persCount input = 0 then 0 else 2) :=
  wideLayout_overhead input base S w ▸ simExecWithinLayout (wideLayout input base S w)
    c retReg argRegs decode defaultAns harg hm hexec


/-! ### 4. Randomized (`ExecRand`) and unbounded Las Vegas (`ExecProgramDist` / `ExecCodeDist`)
simulation in `RandProbeTree` -/

/-- Project a buffered `SimOutcome` over base memory `m` to the corresponding `WordRAM.RandCfg r`.
-/
def SimOutcome.toRandCfg {r S regCells w wCell : ℕ} (base : ℕ)
    (m : Mem (S + regCells) wCell) : SimOutcome S w r → RandCfg r
  | .running pc regs wb ext => .running ⟨pc, reconstructData base m regs wb ext⟩
  | .halted out regs wb ext => .halted out (reconstructData base m regs wb ext)
  | .faulted => .faulted

/-- Number of buffered modified cells carried by a `SimOutcome`. -/
def SimOutcome.dirty {S w r : ℕ} : SimOutcome S w r → ℕ
  | .running _ _ wb _ => dirtyCount wb
  | .halted _ _ wb _ => dirtyCount wb
  | .faulted => 0

/-- Boolean predicate for active configurations not yet positioned at `Instr.halt` (the only
configurations on which `simStepRand` can increase `probes + dirty` by `1`). -/
def isContinuingCfg {B : Basis} {r : ℕ} (p : Program B r) : RandCfg r → Bool
  | .running s =>
    match p[s.pc]? with
    | some (.halt _) => false
    | _ => true
  | _ => false

/-- One step of buffered randomized flat-program simulation in `RandProbeTree`: maps `Instr.rand`
to `0`-probe `RandProbeTree.sample (ProbComp.unifFin ...)` and delegates all other instructions to
`RandProbeTree.ofProbeTree (simStepDet ...)`. -/
def simStepRand {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r) :
    SimOutcome S w r → RandProbeTree (S + regCells) wCell (SimOutcome S w r)
  | .running pc regs writeBuf extMem =>
    match p[pc]? with
    | some (.rand dst src) =>
      if Fits w (regs src) then do
        let k ← RandProbeTree.sample (ProbComp.unifFin (regs src))
        pure (.running (pc + 1) (Function.update regs dst k.val) writeBuf extMem)
      else
        pure .faulted
    | _ => RandProbeTree.ofProbeTree (simStepDet base p (.running pc regs writeBuf extMem))
  | st => pure st

/-- A running configuration is continuing unless its next deterministic step halts. -/
private theorem isContinuingCfg_running_iff {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r)
    (s : State r) :
    isContinuingCfg p (.running s) = true ↔ ∀ v, step w p s ≠ .halt v := by
  rcases hp : p[s.pc]? with _ | (o | _ | _ | _ | _) <;> simp only [isContinuingCfg, step, hp] <;>
    (try split) <;> simp

private theorem simStepRand_spec {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (st : SimOutcome S w r) (m : Mem (S + regCells) wCell)
    (hcfg : (st.toRandCfg (w := w) base m).Bounded w) :
    let t := simStepRand (regCells := regCells) (w := w) (wCell := wCell) base p st
    (t.run m).map (fun z => z.1.1.toRandCfg base m) =
      (stepRand w p (st.toRandCfg base m)).eval ∧
    ∀ z ∈ (t.run m).support,
      z.1.2 = m ∧
      (z.1.1.toRandCfg (w := w) base m).Bounded w ∧
      z.2 + z.1.1.dirty ≤
        (if isContinuingCfg p (st.toRandCfg base m) then 1 else 0) + st.dirty := by
  intro t
  suffices hmain : (t.run m).map (fun z => z.1.1.toRandCfg base m) =
        (stepRand w p (st.toRandCfg base m)).eval ∧
      ∀ z ∈ (t.run m).support, z.1.2 = m ∧ z.2 + z.1.1.dirty ≤
        (if isContinuingCfg p (st.toRandCfg base m) then 1 else 0) + st.dirty from
    ⟨hmain.1, fun z hz => ⟨(hmain.2 z hz).1, stepRand_bounded hcfg (by
      rw [← ProbComp.support_eval, ← hmain.1, PMF.mem_support_map_iff]
      exact ⟨z, hz, rfl⟩), (hmain.2 z hz).2⟩⟩
  cases st with
  | halted out regs wb ext =>
    simp [t, simStepRand, SimOutcome.toRandCfg, stepRand_halted, isContinuingCfg]
  | faulted => simp [t, simStepRand, SimOutcome.toRandCfg, stepRand_faulted, isContinuingCfg]
  | running pc regs wb ext =>
    dsimp only [t, simStepRand, SimOutcome.toRandCfg]
    set x := reconstructData (w := w) base m regs wb ext
    have hx : x.Bounded w := hcfg
    split
    · next dst src hp =>
      have hcont : isContinuingCfg p (.running ⟨pc, x⟩) = true :=
        (isContinuingCfg_running_iff w p _).mpr (by simp [step_rand (s := ⟨pc, x⟩) hp])
      by_cases hfit : Fits w (regs src)
      · simp only [hfit, ↓reduceIte, stepRand_rand_of_fits (s := ⟨pc, x⟩) hp hfit,
          RandProbeTree.run_bind, RandProbeTree.run_sample, PMF.map_bind, PMF.bind_map,
          RandProbeTree.run_pure, PMF.pure_map, ProbComp.eval_pure, ProbComp.eval_bind,
          Function.comp_def, zero_add, PMF.mem_support_bind_iff,
          PMF.support_pure, Set.mem_singleton_iff]
        refine ⟨rfl, ?_⟩
        rintro _ ⟨_, _, rfl⟩
        exact ⟨rfl, by simp [hcont, SimOutcome.dirty]⟩
      · simp [hfit, stepRand_rand_of_not_fits (s := ⟨pc, x⟩) hp hfit, hcont, SimOutcome.dirty]
    · next hnot_rand =>
      obtain ⟨hm_eq, hdet_out⟩ :=
        simStepDet_spec (regCells := regCells) (wCell := wCell) base p pc m hx
      rw [stepRand_eq_ofOutcome_of_ne_rand (s := ⟨pc, x⟩) hnot_rand]
      simp only [RandProbeTree.run_ofProbeTree, PMF.pure_map, ProbComp.eval_pure,
        PMF.support_pure, Set.mem_singleton_iff, forall_eq, hm_eq, true_and]
      revert hdet_out
      cases hs_out : step w p ⟨pc, x⟩ with
      | next s' =>
        rintro ⟨wb', ext', hrun1, hrec', hpr1⟩
        have hcont : isContinuingCfg p (.running ⟨pc, x⟩) = true :=
          (isContinuingCfg_running_iff w p _).mpr (by simp [hs_out])
        simpa [hrun1, hrec', RandCfg.ofOutcome, SimOutcome.toRandCfg, SimOutcome.dirty, hcont]
          using hpr1
      | halt v | fault =>
        rintro ⟨hrun1, hpr1⟩
        simp [hrun1, hpr1, RandCfg.ofOutcome, SimOutcome.dirty, x]

/-- Clocked `K`-step buffered randomized execution in `RandProbeTree`. -/
def simLoopRand {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r) :
    ℕ → SimOutcome S w r → RandProbeTree (S + regCells) wCell (SimOutcome S w r)
  | 0, st => pure st
  | K + 1, st => do
      let st' ← simStepRand base p st
      simLoopRand base p K st'

/-- `simLoopRand` unfolded at its last step. -/
private theorem simLoopRand_succ {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (K : ℕ) (st : SimOutcome S w r) :
    simLoopRand (regCells := regCells) (wCell := wCell) base p (K + 1) st =
      simLoopRand (regCells := regCells) (wCell := wCell) base p K st >>= simStepRand base p := by
  induction K generalizing st with
  | zero => simp [simLoopRand]
  | succ K ih =>
    rw [simLoopRand, simLoopRand, bind_assoc]
    exact congrArg (simStepRand base p st >>= ·) (funext ih)

private theorem simStepRand_worstCase_probes {B : Basis} {r S regCells w wCell : ℕ}
    (base : ℕ) (p : Program B r) (st : SimOutcome S w r) (m : Mem (S + regCells) wCell) :
    ∀ z ∈ ((simStepRand (regCells := regCells) (w := w) (wCell := wCell) base p st).run m).support,
      z.1.2 = m ∧ z.2 ≤ 1 := by
  cases st with
  | running pc regs wb ext =>
    dsimp only [simStepRand]
    split
    · split_ifs <;> simp
    · simp [simStepDet_nextMem_probes]
  | _ => simp [simStepRand]

private theorem simLoopRand_worstCase_probes {B : Basis} {r S regCells w wCell : ℕ}
    (base : ℕ) (p : Program B r) (K : ℕ) (st : SimOutcome S w r) (m : Mem (S + regCells) wCell) :
    ∀ z ∈
      ((simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K st).run m).support,
      z.1.2 = m ∧ z.2 ≤ K := by
  induction K generalizing st with
  | zero => simp [simLoopRand]
  | succ K ih =>
    intro z hz
    simp only [simLoopRand, RandProbeTree.run_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hz
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hz
    obtain ⟨hm₁, hpr₁⟩ := simStepRand_worstCase_probes base p st m z₁ hz₁
    rw [hm₁] at hz₂
    obtain ⟨hm₂, hpr₂⟩ := ih z₁.1.1 z₂ hz₂
    exact ⟨hm₂, by omega⟩

private theorem simLoopRand_spec {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (K : ℕ) (st : SimOutcome S w r) (m : Mem (S + regCells) wCell)
    (hcfg : (st.toRandCfg (w := w) base m).Bounded w) :
    let loop := simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K st
    (loop.run m).map (fun z => z.1.1.toRandCfg base m) =
      (runRand w p K (st.toRandCfg base m)).eval ∧
    (∀ z ∈ (loop.run m).support, z.1.2 = m ∧ (z.1.1.toRandCfg (w := w) base m).Bounded w) ∧
    (∑' z, (loop.run m) z * ((z.2 + z.1.1.dirty : ℕ) : ℝ≥0∞)) ≤
      (st.dirty : ℝ≥0∞) +
        ∑ t ∈ Finset.range K,
          (runRand w p t (st.toRandCfg base m)).eval.toOuterMeasure
            {cfg | isContinuingCfg p cfg = true} := by
  induction K with
  | zero =>
    refine ⟨by simp [simLoopRand], by simpa [simLoopRand] using hcfg,
      (Probability.PMF.tsum_mul_le_of_support _ fun z hz => ?_).trans le_self_add⟩
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hz
    simp
  | succ K ih =>
    obtain ⟨hmap_K, hsup_K, hexp_K⟩ := ih
    simp only [simLoopRand_succ]
    set loop_K := simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K st
    refine ⟨?_, ?_, ?_⟩
    · rw [RandProbeTree.run_bind, PMF.map_bind, runRand_add w p K 1, ProbComp.eval_bind, ← hmap_K,
        PMF.bind_map]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨st₁, m₁⟩, p₁⟩ hz₁ => ?_
      obtain ⟨rfl, hbdd₁⟩ := hsup_K _ hz₁
      dsimp only [Function.comp_apply]
      rw [PMF.map_comp, runRand_succ]
      simp only [runRand_zero, bind_pure]
      exact (simStepRand_spec base p st₁ m₁ hbdd₁).1
    · intro z hz
      simp only [RandProbeTree.run_bind, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hz
      obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hz
      obtain ⟨hm₁, hbdd₁⟩ := hsup_K z₁ hz₁
      rw [hm₁] at hz₂
      obtain ⟨hm₂, hbdd₂, -⟩ := (simStepRand_spec base p z₁.1.1 m hbdd₁).2 z₂ hz₂
      exact ⟨hm₂, hbdd₂⟩
    · rw [RandProbeTree.run_bind, Probability.PMF.tsum_bind_mul]
      calc _ ≤ ∑' z₁, (loop_K.run m) z₁ * (((z₁.2 + z₁.1.1.dirty : ℕ) : ℝ≥0∞) +
              Set.indicator {cfg | isContinuingCfg p cfg = true} 1 (z₁.1.1.toRandCfg base m)) :=
            Probability.PMF.tsum_mul_mono_support _ fun ⟨⟨st₁, m₁⟩, p₁⟩ hz₁ => ?_
        _ ≤ _ := by
            simp only [mul_add]
            rw [tsum_add, Finset.sum_range_succ, ← add_assoc, ← hmap_K,
              Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator, Probability.PMF.tsum_map_mul]
            exact add_le_add hexp_K le_rfl
      obtain ⟨rfl, hbdd₁⟩ := hsup_K _ hz₁
      dsimp only
      rw [Probability.PMF.tsum_map_mul]
      refine Probability.PMF.tsum_mul_le_of_support _ fun z₂ hz₂ => ?_
      obtain ⟨-, -, hpr₂⟩ := (simStepRand_spec base p st₁ m₁ hbdd₁).2 z₂ hz₂
      calc ((p₁ + z₂.2 + z₂.1.1.dirty : ℕ) : ℝ≥0∞)
          ≤ ((p₁ + st₁.dirty +
              if isContinuingCfg p (st₁.toRandCfg base m₁) then 1 else 0 : ℕ) : ℝ≥0∞) :=
            Nat.cast_le.mpr (by omega)
        _ = _ := by simp [Set.indicator_apply]

/-! #### Exact telescoping of the `.halt` instruction step -/

/-- One-step mass balance, by cases on the outcome of the step: a configuration either continues
or lands in `haltedSet` after one step exactly when it is running or already halted. -/
private theorem stepRand_haltedSet_identity {B : Basis} {r w : ℕ} (p : Program B r)
    (cfg : RandCfg r) :
    Set.indicator {c | isContinuingCfg p c = true} (1 : RandCfg r → ℝ≥0∞) cfg +
        (stepRand w p cfg).eval.toOuterMeasure (RandCfg.haltedSet r) =
      Set.indicator (RandCfg.runningSet r) (1 : RandCfg r → ℝ≥0∞) cfg +
        Set.indicator (RandCfg.haltedSet r) (1 : RandCfg r → ℝ≥0∞) cfg := by
  rcases cfg with s | ⟨v, d⟩ | _
  · by_cases hrand : ∃ dst src, p[s.pc]? = some (.rand dst src)
    · obtain ⟨dst, src, hp⟩ := hrand
      by_cases hfit : Fits w (s.data.regs src) <;>
        simp [isContinuingCfg_running_iff w p s, step_rand hp, stepRand_rand_of_fits hp,
          stepRand_rand_of_not_fits hp, hfit, PMF.toOuterMeasure_pure_apply]
    · rw [stepRand_eq_ofOutcome_of_ne_rand fun dst src h => hrand ⟨dst, src, h⟩]
      cases hs : step w p s <;>
        simp [isContinuingCfg_running_iff w p s, hs, RandCfg.ofOutcome,
          PMF.toOuterMeasure_pure_apply]
  · simp [show isContinuingCfg p (.halted v d) = false from rfl, stepRand_halted,
      PMF.toOuterMeasure_pure_apply]
  · simp [show isContinuingCfg p .faulted = false from rfl, stepRand_faulted,
      PMF.toOuterMeasure_pure_apply]

/-- `evalRand` unfolded at its last step. -/
private theorem evalRand_succ_right {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (K : ℕ)
    (s : State r) :
    evalRand w p (K + 1) s = (evalRand w p K s).bind fun cfg => (stepRand w p cfg).eval := by
  rw [evalRand, runRand_add w p K 1, ProbComp.eval_bind]
  simp only [evalRand, runRand_succ, runRand_zero, bind_pure]

theorem continuing_sum_add_halted_eq_running_sum {B : Basis} {r w : ℕ} (p : Program B r)
    (s₀ : State r) (K : ℕ) :
    (∑ t ∈ Finset.range K,
        (evalRand w p t s₀).toOuterMeasure {cfg | isContinuingCfg p cfg = true}) +
      (evalRand w p K s₀).toOuterMeasure (RandCfg.haltedSet r) =
      ∑ t ∈ Finset.range K, (evalRand w p t s₀).toOuterMeasure (RandCfg.runningSet r) := by
  induction K with
  | zero => simp [PMF.toOuterMeasure_pure_apply]
  | succ K ih =>
    have hstep_rel :
        (evalRand w p K s₀).toOuterMeasure {cfg | isContinuingCfg p cfg = true} +
          (evalRand w p (K + 1) s₀).toOuterMeasure (RandCfg.haltedSet r) =
        (evalRand w p K s₀).toOuterMeasure (RandCfg.runningSet r) +
          (evalRand w p K s₀).toOuterMeasure (RandCfg.haltedSet r) := by
      rw [evalRand_succ_right, PMF.toOuterMeasure_bind_apply]
      simp only [Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator (evalRand w p K s₀),
        ← tsum_add, ← mul_add, stepRand_haltedSet_identity]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_assoc, hstep_rel,
      ← add_assoc, add_right_comm _ _ ((evalRand w p K s₀).toOuterMeasure (RandCfg.haltedSet r)),
      ih]

theorem continuing_sum_le_of_almostSurelyHalts {B : Basis} {r w : ℕ} {p : Program B r}
    {s₀ : State r} {T : ℝ≥0∞} (has : AlmostSurelyHalts w p s₀)
    (hexp : expectedTime w p s₀ ≤ T + 1) (K : ℕ) :
    (∑ t ∈ Finset.range K,
        (evalRand w p t s₀).toOuterMeasure {cfg | isContinuingCfg p cfg = true}) ≤ T := by
  refine (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp ?_
  conv_lhs => rw [← has.2, ENNReal.add_iSup]
  refine iSup_le fun M => ?_
  calc _ ≤ (∑ t ∈ Finset.range (max K M),
          (evalRand w p t s₀).toOuterMeasure {cfg | isContinuingCfg p cfg = true}) +
        (evalRand w p (max K M) s₀).toOuterMeasure (RandCfg.haltedSet r) :=
      add_le_add (Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left K M)))
        (evalRand_haltedSet_mono w p s₀ (le_max_right K M))
    _ = _ := continuing_sum_add_halted_eq_running_sum p s₀ _
    _ ≤ T + 1 := (sum_le_tsum _).trans hexp

/-! #### Halting-limit identification, `ExecProgramDist`, and zero-error fallback -/

/-- Supremum halting probability of `p` from `⟨0, x⟩` at `(vy.1, vy.2)`. -/
@[expose] noncomputable def haltedLim {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (x : Data r)
    (vy : ℕ × Data r) : ℝ≥0∞ :=
  ⨆ K : ℕ, evalRand w p K ⟨0, x⟩ (.halted vy.1 vy.2)

private theorem halted_injective {r : ℕ} :
    Function.Injective fun vy : ℕ × Data r => RandCfg.halted vy.1 vy.2 :=
  fun ⟨_, _⟩ ⟨_, _⟩ h => by cases h; rfl

private theorem tsum_haltedLim_eq_iSup {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (x : Data r) :
    (∑' vy : ℕ × Data r, haltedLim w p x vy) =
      ⨆ K : ℕ, ∑' vy : ℕ × Data r, evalRand w p K ⟨0, x⟩ (.halted vy.1 vy.2) :=
  ENNReal.tsum_iSup_of_monotone
    (f := fun K (vy : ℕ × Data r) => evalRand w p K ⟨0, x⟩ (.halted vy.1 vy.2))
    fun vy => evalRand_halted_mono w p ⟨0, x⟩ vy.1 vy.2

/-- A weight function of total mass at most `1` that dominates a `PMF` pointwise equals it. -/
private theorem eq_of_pmf_le {α : Type*} (μ : PMF α) {f : α → ℝ≥0∞} (hle : ∀ a, μ a ≤ f a)
    (hf : ∑' a, f a ≤ 1) (a : α) : f a = μ a :=
  le_antisymm (le_of_not_gt fun hlt =>
    (ENNReal.tsum_lt_tsum μ.tsum_coe_ne_top hle hlt).not_ge (hf.trans_eq μ.tsum_coe.symm)) (hle a)

theorem tsum_haltedLim_le_one {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (x : Data r) :
    (∑' vy : ℕ × Data r, haltedLim w p x vy) ≤ 1 := by
  rw [tsum_haltedLim_eq_iSup]
  exact iSup_le fun K => (tsum_comp_le_tsum_of_injective halted_injective _).trans_eq
    (evalRand w p K ⟨0, x⟩).tsum_coe

/-- Distributional execution contract for a flat `WordRAM.Program B r`: from `⟨0, x⟩`, `p` never
faults, has expected instruction count at most `T`, and dominates `μ : PMF (ℕ × Data r)` at its
supremum halting probabilities. Because `∑' vy, μ vy = 1` and `∑' vy, haltedLim w p x vy ≤ 1`,
domination forces exact equality `haltedLim w p x vy = μ vy` (`ExecProgramDist.haltedLim_eq`) and
almost-sure halting (`ExecProgramDist.almostSurelyHalts`). -/
@[expose] def ExecProgramDist {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (x : Data r)
    (μ : PMF (ℕ × Data r)) (T : ℝ≥0∞) : Prop :=
  expectedTime w p ⟨0, x⟩ ≤ T ∧
  RandFaultFree w p ⟨0, x⟩ ∧
  ∀ vy : ℕ × Data r, μ vy ≤ haltedLim w p x vy

namespace ExecProgramDist

variable {B : Basis} {r w : ℕ} {p : Program B r} {x : Data r} {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞}

theorem haltedLim_eq (h : ExecProgramDist w p x μ T) (vy : ℕ × Data r) :
    haltedLim w p x vy = μ vy :=
  eq_of_pmf_le μ h.2.2 (tsum_haltedLim_le_one w p x) vy

theorem evalRand_halted_le (h : ExecProgramDist w p x μ T) (K : ℕ) (vy : ℕ × Data r) :
    evalRand w p K ⟨0, x⟩ (.halted vy.1 vy.2) ≤ μ vy := by
  rw [← h.haltedLim_eq vy]
  exact le_iSup (fun k => evalRand w p k ⟨0, x⟩ (.halted vy.1 vy.2)) K

theorem almostSurelyHalts (h : ExecProgramDist w p x μ T) :
    AlmostSurelyHalts w p ⟨0, x⟩ := by
  refine ⟨h.2.1, le_antisymm
    (iSup_le fun _ => Probability.PMF.toOuterMeasure_le_one _ _) ?_⟩
  calc (1 : ℝ≥0∞) = ∑' vy : ℕ × Data r, haltedLim w p x vy := by
        simp_rw [h.haltedLim_eq, μ.tsum_coe]
    _ = _ := tsum_haltedLim_eq_iSup w p x
    _ ≤ _ := iSup_mono fun K => ?_
  rw [PMF.toOuterMeasure_apply]
  refine (tsum_le_tsum fun vy : ℕ × Data r => ?_).trans
    (tsum_comp_le_tsum_of_injective halted_injective
      (Set.indicator (RandCfg.haltedSet r) (evalRand w p K ⟨0, x⟩)))
  exact (Set.indicator_of_mem (s := RandCfg.haltedSet r) ⟨vy.1, vy.2, rfl⟩ _).ge

end ExecProgramDist

/-- Lift a structured `ExecCodeDist w c x μ T` certificate to `ExecProgramDist` on `c.program out`.
-/
theorem execProgramDist_of_execCodeDist {B : Basis} {r w : ℕ} {c : Code B r} {x : Data r}
    {μ : PMF (Data r)} {T : ℝ≥0∞} (h : ExecCodeDist w c x μ T) (out : Fin r) :
    ExecProgramDist w (c.program out) x (μ.map fun y => (y.regs out, y)) (T + 1) := by
  obtain ⟨hexp, hff, _, hdom⟩ := h.program_halts out
  refine ⟨hexp, hff, fun ⟨v, y⟩ => ?_⟩
  by_cases hv : v = y.regs out
  · subst hv
    exact (Probability.PMF.map_apply_of_injective μ (f := fun y : Data r => (y.regs out, y))
      (fun _ _ h => (Prod.mk.inj h).2) y).trans_le (hdom y)
  · refine ((PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_).trans_le zero_le
    obtain ⟨a, -, ha⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
    cases ha
    exact hv rfl

/-- Pure-Lean fallback halting outcome for `p` from `⟨0, x⟩`: selects a reachable `(v, y)` with
positive halting limit `0 < haltedLim w p x (v, y)` when one exists, or `(0, x)` otherwise. -/
noncomputable def fallbackOutcome {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (x : Data r) :
    ℕ × Data r :=
  letI := Classical.propDecidable
  if h : ∃ vy : ℕ × Data r, 0 < haltedLim w p x vy then Classical.choose h else (0, x)

theorem fallbackOutcome_mem_support {B : Basis} {r w : ℕ} {p : Program B r} {x : Data r}
    {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞} (h : ExecProgramDist w p x μ T) :
    fallbackOutcome w p x ∈ μ.support := by
  obtain ⟨vy₀, hvy₀⟩ := μ.support_nonempty
  have hex : ∃ vy : ℕ × Data r, 0 < haltedLim w p x vy :=
    ⟨vy₀, (h.haltedLim_eq vy₀).symm ▸ pos_iff_ne_zero.mpr hvy₀⟩
  rw [fallbackOutcome, dite_eq_left hex, PMF.mem_support_iff, ← h.haltedLim_eq]
  exact (Classical.choose_spec hex).ne'

/-- Buffered finite-horizon `RandProbeTree` simulator for a flat `WordRAM.Program B r`:
1. Reloads persistent registers via `L.reload argRegs` (`regs₀ = (L.unpack argRegs m).regs`).
2. Runs `K` buffered steps via `simLoopRand` without mutating cell memory `m`.
3. On `.halted v regs' writeBuf' _`, flushes `writeBuf'` and spills persistent registers via
   `commitHalted`.
4. On the `> K` tail (`.running`), reads the `S` untouched data cells of `m`, reconstructs
   `x₀ = L.unpack argRegs m` in pure Lean, selects `vy = fallbackOutcome w p x₀` (`∈ μ.support`!),
   and writes `L.pack vy.2` (`2 * S + regCells` probes on the tail), preserving **100% zero-error
   support correctness** at finite tree depth. -/
noncomputable def simProgRand {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ) :
    RandProbeTree (S + regCells) wCell Out := do
  let regs₀ ← RandProbeTree.ofProbeTree (L.reload argRegs)
  let out ← simLoopRand base p K (.running 0 regs₀ (fun _ => none) (fun _ => 0))
  match out with
  | .halted v regs' writeBuf' _ =>
    let _ ← RandProbeTree.ofProbeTree (commitHalted L regs' writeBuf')
    pure ((decode v regs').getD defaultAns)
  | _ =>
    let dataVals ← RandProbeTree.ofProbeTree
      (readFin (fun j : Fin S => Fin.castAdd regCells j))
    let x₀ : Data r :=
      { regs := regs₀
        mem := fun a =>
          if ha : base ≤ a ∧ a < base + S then
            (dataVals ⟨a - base, by omega⟩).val % 2 ^ w
          else 0 }
    let vy := fallbackOutcome w p x₀
    let _ ← RandProbeTree.ofProbeTree (writeFin (fun c => c) (L.pack vy.2))
    pure ((decode vy.1 vy.2.regs).getD defaultAns)

/-- Post-loop completion step of `simProgRand`, factored for clean expectation analysis. -/
private noncomputable def finishSimProgRand {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (regs₀ : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) :
    SimOutcome S w r → RandProbeTree (S + regCells) wCell Out
  | .halted v regs' writeBuf' _ => do
      let _ ← RandProbeTree.ofProbeTree (commitHalted L regs' writeBuf')
      pure ((decode v regs').getD defaultAns)
  | _ => do
      let dataVals ← RandProbeTree.ofProbeTree
        (readFin (fun j : Fin S => Fin.castAdd regCells j))
      let x₀ : Data r :=
        { regs := regs₀
          mem := fun a =>
            if ha : base ≤ a ∧ a < base + S then
              (dataVals ⟨a - base, by omega⟩).val % 2 ^ w
            else 0 }
      let vy := fallbackOutcome w p x₀
      let _ ← RandProbeTree.ofProbeTree (writeFin (fun c => c) (L.pack vy.2))
      pure ((decode vy.1 vy.2.regs).getD defaultAns)

private theorem simProgRand_eq_bind {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ) :
    simProgRand (w := w) L p argRegs decode defaultAns K = (do
      let regs₀ ← RandProbeTree.ofProbeTree (L.reload argRegs)
      let out ← simLoopRand base p K (.running 0 regs₀ (fun _ => none) (fun _ => 0))
      finishSimProgRand (w := w) L p regs₀ decode defaultAns out) := by
  refine congrArg (RandProbeTree.ofProbeTree (L.reload argRegs) >>= ·) (funext fun regs₀ => ?_)
  refine congrArg (simLoopRand base p K (.running 0 regs₀ (fun _ => none) (fun _ => 0)) >>= ·)
    (funext fun out => ?_)
  cases out <;> rfl

private theorem finishSimProgRand_fallback_run {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (m : Mem (S + regCells) wCell) (out : SimOutcome S w r)
    (hnot_halt : ∀ v regs' wb' ext', out ≠ .halted v regs' wb' ext') :
    (finishSimProgRand (w := w) L p (L.unpack argRegs m).regs decode defaultAns out).run m =
      PMF.pure
        (((decode (fallbackOutcome w p (L.unpack argRegs m)).1
            (fallbackOutcome w p (L.unpack argRegs m)).2.regs).getD defaultAns,
          L.pack (fallbackOutcome w p (L.unpack argRegs m)).2),
         2 * S + regCells) := by
  have hx₀_eq :
      ({ regs := (L.unpack argRegs m).regs
         mem := fun a =>
           if ha : base ≤ a ∧ a < base + S then
             (m (Fin.castAdd regCells ⟨a - base, by omega⟩)).val % 2 ^ w
           else 0 } : Data r) = L.unpack argRegs m :=
    Data.ext rfl (funext fun a => (L.unpack_mem argRegs m a).symm)
  cases out with
  | halted v regs' wb' ext' => exact absurd rfl (hnot_halt v regs' wb' ext')
  | running _ _ _ _ | faulted =>
    simp only [finishSimProgRand, RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree,
      PMF.pure_bind, run_readFin, probes_readFin, RandProbeTree.run_pure, PMF.pure_map, add_zero,
      probes_writeFin, nextMem_writeFin_id, hx₀_eq]
    exact congrArg PMF.pure (Prod.ext rfl (by omega))

/-- Unconditional worst-case probe bound for `simProgRand` on **any** memory `m`: every path issues
at most `K + 2 * S + regCells + L.overhead` cell probes. -/
theorem simProgRand_worstCase_probes {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ)
    (m : Mem (S + regCells) wCell) :
    ∀ z ∈ ((simProgRand (w := w) L p argRegs decode defaultAns K).run m).support,
      z.2 ≤ K + 2 * S + regCells + L.overhead := by
  intro z hz
  rw [simProgRand_eq_bind] at hz
  simp only [RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree, L.run_reload,
    L.probes_reload, PMF.pure_bind, PMF.mem_support_map_iff, PMF.mem_support_bind_iff] at hz
  obtain ⟨z_mid, ⟨z_loop, hz_loop, z_fin, hz_fin, rfl⟩, rfl⟩ := hz
  obtain ⟨hm_loop, hpr_loop⟩ := simLoopRand_worstCase_probes base p K _ m z_loop hz_loop
  rw [hm_loop] at hz_fin
  have hov : L.overhead = L.reloadProbes + L.spillProbes := rfl
  cases hout : z_loop.1.1 with
  | halted v regs' wb' ext' =>
    have hdirty_le : dirtyCount wb' ≤ S := by
      simpa [dirtyCount] using Finset.card_filter_le (Finset.univ : Finset (Fin S)) _
    simp only [hout, finishSimProgRand, RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree,
      PMF.pure_bind, RandProbeTree.run_pure, PMF.pure_map, add_zero, PMF.support_pure,
      Set.mem_singleton_iff, commitHalted, ProbeTree.probes_bind, probes_flushWriteBuf,
      L.probes_spill] at hz_fin
    subst hz_fin
    omega
  | _ =>
    rw [hout, finishSimProgRand_fallback_run L p argRegs decode defaultAns m _ (by simp),
      PMF.support_pure, Set.mem_singleton_iff] at hz_fin
    subst hz_fin
    omega

theorem simProgRand_expectedProbes_le_worstCase {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ)
    (m : Mem (S + regCells) wCell) :
    (simProgRand (w := w) L p argRegs decode defaultAns K).expectedProbes m ≤
      ((K + 2 * S + regCells + L.overhead : ℕ) : ℝ≥0∞) :=
  Probability.PMF.tsum_mul_le_of_support _ fun z hz =>
    Nat.cast_le.mpr (simProgRand_worstCase_probes L p argRegs decode defaultAns K m z hz)

/-- Loop-level facts for the initial configuration of `simProgRand`: the buffered `K`-step loop
projects onto `evalRand w p K`, and its expected `probes + dirty` count is at most the expected
number of continuing steps. -/
private theorem simLoopRand_init {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ) (K : ℕ) (m : Mem (S + regCells) wCell)
    (harg : ∀ i, input i = true → Fits w (argRegs i)) :
    let loop := simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K
      (.running 0 (L.unpack argRegs m).regs (fun _ => none) (fun _ => 0))
    (loop.run m).map (fun z => z.1.1.toRandCfg base m) = evalRand w p K ⟨0, L.unpack argRegs m⟩ ∧
    (∑' z, (loop.run m) z * ((z.2 + z.1.1.dirty : ℕ) : ℝ≥0∞)) ≤
      ∑ t ∈ Finset.range K, (evalRand w p t ⟨0, L.unpack argRegs m⟩).toOuterMeasure
        {cfg | isContinuingCfg p cfg = true} := by
  have hst₀ : (SimOutcome.running 0 (L.unpack argRegs m).regs (fun _ => none)
      (fun _ => 0)).toRandCfg (w := w) base m = .running ⟨0, L.unpack argRegs m⟩ := by
    simp [SimOutcome.toRandCfg, reconstructData_init L argRegs m]
  obtain ⟨hmap, -, hexp⟩ := simLoopRand_spec (regCells := regCells) (wCell := wCell) base p K _ m
    (by rw [hst₀]; exact L.unpack_bounded harg m)
  rw [hst₀] at hmap hexp
  simp only [SimOutcome.dirty, dirtyCount_empty, Nat.cast_zero, zero_add] at hexp
  exact ⟨hmap, hexp⟩

/-- Closed form of a `simProgRand` run on valid memory: the loop outcome determines the result
(the halting pair, or the fallback pair when the loop did not halt) and the probe count. -/
private theorem simProgRand_run {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m) :
    (simProgRand (w := w) L p argRegs decode defaultAns K).run m =
      ((simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K
        (.running 0 (L.unpack argRegs m).regs (fun _ => none) (fun _ => 0))).run m).map fun z =>
        ((fun vy : ℕ × Data r => ((decode vy.1 vy.2.regs).getD defaultAns, L.pack vy.2))
            (match z.1.1.toRandCfg base m with
              | .halted v y => (v, y)
              | _ => fallbackOutcome w p (L.unpack argRegs m)),
          L.reloadProbes + z.2 +
            match z.1.1 with
            | .halted _ _ wb _ => dirtyCount wb + L.spillProbes
            | _ => 2 * S + regCells) := by
  rw [simProgRand_eq_bind, RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree, L.run_reload,
    L.probes_reload, PMF.pure_bind]
  dsimp only
  rw [RandProbeTree.run_bind, PMF.map_bind, ← PMF.bind_pure_comp]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨st_l, m_l⟩, p_l⟩ hz_l => ?_
  obtain rfl : m = m_l := (simLoopRand_worstCase_probes base p K _ m _ hz_l).1.symm
  dsimp only [Function.comp_apply]
  cases st_l with
  | halted v regs' wb' ext' =>
    obtain ⟨hcm_mem, hcm_pr⟩ := commitHalted_spec L hm regs' wb' ext'
    simp only [finishSimProgRand, RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree,
      PMF.pure_bind, RandProbeTree.run_pure, PMF.pure_map, add_zero, hcm_mem, hcm_pr]
    exact congrArg PMF.pure (Prod.ext rfl (Nat.add_assoc _ _ _).symm)
  | _ =>
    rw [finishSimProgRand_fallback_run L p argRegs decode defaultAns m _ (by simp), PMF.pure_map,
      PMF.pure_map]
    exact congrArg PMF.pure (Prod.ext rfl (Nat.add_assoc _ _ _).symm)

/-- Output law of `simProgRand` on valid memory: the image of the `K`-step configuration law
`evalRand w p K` under "halting pair, else fallback pair", then decoded and packed. -/
private theorem simProgRand_law {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (harg : ∀ i, input i = true → Fits w (argRegs i)) :
    ((simProgRand (w := w) L p argRegs decode defaultAns K).run m).map Prod.fst =
      ((evalRand w p K ⟨0, L.unpack argRegs m⟩).map fun cfg =>
        match cfg with
        | .halted v y => (v, y)
        | _ => fallbackOutcome w p (L.unpack argRegs m)).map fun vy =>
          ((decode vy.1 vy.2.regs).getD defaultAns, L.pack vy.2) := by
  rw [simProgRand_run L p argRegs decode defaultAns K hm,
    ← (simLoopRand_init L p argRegs K m harg).1, PMF.map_comp, PMF.map_comp, PMF.map_comp]
  rfl

/-- **Main single-step Las Vegas simulation theorem (`simProgRand_lasVegas_spec`):**
Under `hm : L.ValidMem m`, `harg`, and `hdist : ExecProgramDist w p (L.unpack argRegs m) μ T`:
1. **100% zero-error support soundness (at any finite `K`):** every outcome `(ans, m')` in the
   support of `(simProgRand L p argRegs decode defaultAns K).run m` comes from some
   `vy ∈ μ.support` with `ans = (decode vy.1 vy.2.regs).getD defaultAns` and `m' = L.pack vy.2`!
2. **Expected probe bound:**
   `expectedProbes ≤ continuingSum K + L.overhead + p_run(K) * (2 * S + regCells)`.
3. **Continuation coupling inequality:** for any bounded continuation `g ≤ B_rem` on support,
   `E_{simProgRand}[g] ≤ E_{vy ~ μ}[g (decode vy, L.pack vy.2)] + p_run(K) * B_rem`! -/
theorem simProgRand_lasVegas_spec {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞}
    (hdist : ExecProgramDist w p (L.unpack argRegs m) μ T) :
    let x₀ := L.unpack argRegs m
    let tree := simProgRand (w := w) L p argRegs decode defaultAns K
    let p_run := (evalRand w p K ⟨0, x₀⟩).toOuterMeasure (RandCfg.runningSet r)
    (∀ z ∈ (tree.run m).support,
      ∃ vy ∈ μ.support, z.1 = ((decode vy.1 vy.2.regs).getD defaultAns, L.pack vy.2)) ∧
    tree.expectedProbes m ≤
      (∑ t ∈ Finset.range K,
          (evalRand w p t ⟨0, x₀⟩).toOuterMeasure {cfg | isContinuingCfg p cfg = true}) +
        (L.overhead : ℝ≥0∞) + p_run * ((2 * S + regCells : ℕ) : ℝ≥0∞) ∧
    ∀ (g : Out × Mem (S + regCells) wCell → ℝ≥0∞) (B_rem : ℝ≥0∞),
      (∀ om ∈ ((tree.run m).map Prod.fst).support, g om ≤ B_rem) →
      (∑' om, ((tree.run m).map Prod.fst) om * g om) ≤
        (∑' vy, μ vy * g ((decode vy.1 vy.2.regs).getD defaultAns, L.pack vy.2)) +
          p_run * B_rem := by
  dsimp only
  set x₀ := L.unpack argRegs m
  obtain ⟨hmap_loop, hexp_loop⟩ := simLoopRand_init L p argRegs K m harg
  set loop := simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K
    (.running 0 x₀.regs (fun _ => none) (fun _ => 0))
  have hlaw := simProgRand_law L p argRegs decode defaultAns K hm harg
  refine ⟨fun z hz => ?_, ?_, fun g B_rem hg_le => ?_⟩
  · -- Part 1: zero-error support soundness.
    have hz' := (PMF.mem_support_map_iff Prod.fst _ z.1).mpr ⟨z, hz, rfl⟩
    rw [hlaw, PMF.mem_support_map_iff] at hz'
    obtain ⟨vy, hvy, hvy_eq⟩ := hz'
    obtain ⟨cfg, hcfg, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hvy
    refine ⟨_, ?_, hvy_eq.symm⟩
    cases cfg with
    | halted v y =>
      exact (PMF.mem_support_iff _ _).mpr fun h0 =>
        hcfg (nonpos_iff_eq_zero.mp ((hdist.evalRand_halted_le K (v, y)).trans_eq h0))
    | _ => exact fallbackOutcome_mem_support hdist
  · -- Part 2: expected probe bound.
    rw [RandProbeTree.expectedProbes, simProgRand_run L p argRegs decode defaultAns K hm,
      Probability.PMF.tsum_map_mul]
    have hov : L.overhead = L.reloadProbes + L.spillProbes := rfl
    calc _ ≤ ∑' z, (loop.run m) z * (((z.2 + z.1.1.dirty : ℕ) : ℝ≥0∞) + (L.overhead : ℝ≥0∞) +
            Set.indicator (RandCfg.runningSet r) 1 (z.1.1.toRandCfg base m) *
              ((2 * S + regCells : ℕ) : ℝ≥0∞)) :=
          Probability.PMF.tsum_mul_mono_support _ fun ⟨⟨st_l, m_l⟩, p_l⟩ hz_l => ?_
      _ ≤ _ := by
          simp only [mul_add, ← mul_assoc]
          rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
            (loop.run m).tsum_coe, one_mul, ← hmap_loop,
            Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator, Probability.PMF.tsum_map_mul]
          exact add_le_add (add_le_add hexp_loop le_rfl) le_rfl
    cases st_l with
    | faulted =>
      refine absurd ?_ (hdist.2.1 K)
      rw [← support_evalRand, ← hmap_loop, PMF.mem_support_map_iff]
      exact ⟨_, hz_l, rfl⟩
    | halted v regs' wb' ext' =>
      rw [Set.indicator_of_notMem (by simp [SimOutcome.toRandCfg])]
      simp only [SimOutcome.dirty, Nat.cast_add]
      exact_mod_cast (by omega)
    | running pc regs' wb' ext' =>
      rw [Set.indicator_of_mem (by simp [SimOutcome.toRandCfg])]
      simp only [SimOutcome.dirty, Nat.cast_add, Pi.one_apply]
      exact_mod_cast (by omega)
  · -- Part 3: continuation coupling inequality.
    rw [hlaw] at hg_le ⊢
    rw [Probability.PMF.tsum_map_mul, Probability.PMF.tsum_map_mul]
    set f_om : ℕ × Data r → Out × Mem (S + regCells) wCell :=
      fun vy => ((decode vy.1 vy.2.regs).getD defaultAns, L.pack vy.2)
    calc _ ≤ ∑' cfg, (evalRand w p K ⟨0, x₀⟩) cfg *
            ((match cfg with
              | .halted v y => g (f_om (v, y))
              | _ => 0) + Set.indicator (RandCfg.runningSet r) 1 cfg * B_rem) :=
          Probability.PMF.tsum_mul_mono_support _ fun cfg hcfg => ?_
      _ = (∑' vy : ℕ × Data r, evalRand w p K ⟨0, x₀⟩ (.halted vy.1 vy.2) * g (f_om vy)) +
            (evalRand w p K ⟨0, x₀⟩).toOuterMeasure (RandCfg.runningSet r) * B_rem := by
          simp only [mul_add, ← mul_assoc]
          rw [tsum_add, ENNReal.tsum_mul_right,
            ← Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator]
          refine congrArg (· + _) (halted_injective.tsum_eq fun cfg hcfg => ?_).symm
          cases cfg with
          | halted v y => exact ⟨(v, y), rfl⟩
          | _ => exact absurd (mul_zero _) hcfg
      _ ≤ _ := add_le_add
          (tsum_le_tsum fun vy => mul_le_mul' (hdist.evalRand_halted_le K vy) le_rfl) le_rfl
    cases cfg with
    | halted v y => exact le_self_add
    | running s =>
      simpa using hg_le _ ((PMF.mem_support_map_iff _ _ _).mpr
        ⟨_, (PMF.mem_support_map_iff _ _ _).mpr ⟨_, hcfg, rfl⟩, rfl⟩)
    | faulted => exact absurd (support_evalRand w p K _ ▸ hcfg) (hdist.2.1 K)

/-! #### Exact finite-tree `ExecRand` simulation (`simExecRand`, `simExecRandWide`) -/

/-- Maximum step count across all leaves of a finite `ProbComp (α × ℕ)` computation tree. -/
noncomputable def probCompMaxSnd {α : Type} : ProbComp (α × ℕ) → ℕ
  | .pure z => z.2
  | .liftBind n cont => Finset.univ.sup fun c : Fin (n + 1) => probCompMaxSnd (cont c)

theorem snd_le_probCompMaxSnd {α : Type} :
    ∀ (m : ProbComp (α × ℕ)) {z : α × ℕ}, z ∈ m.support → z.2 ≤ probCompMaxSnd m
  | .pure w, z, hz => by
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact le_rfl
  | .liftBind n cont, z, hz => by
    obtain ⟨c, -, hc⟩ := (PMF.mem_support_bind_iff _ _ _).mp (ProbComp.support_eval _ ▸ hz)
    exact (snd_le_probCompMaxSnd (cont c) ((ProbComp.support_eval _).symm ▸ hc)).trans
      (Finset.le_sup (f := fun c' : Fin (n + 1) => probCompMaxSnd (cont c')) (Finset.mem_univ c))

/-- Uniform finite-tree fuel across all `m : Mem (S + regCells) wCell` on which `ExecRand` holds. -/
noncomputable def autoRandFuel {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (c : Code B r) (argRegs : Fin r → ℕ) : ℕ :=
  Finset.univ.sup fun m : Mem (S + regCells) wCell =>
    letI := Classical.propDecidable
    if h : ∃ mc : ProbComp (Data r × ℕ), ExecRand w c (L.unpack argRegs m) mc then
      probCompMaxSnd (Classical.choose h) + 1
    else 0

theorem le_autoRandFuel_of_execRand {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ}
    (L : RegLayout r input base S w regCells wCell)
    {c : Code B r} {argRegs : Fin r → ℕ} {m : Mem (S + regCells) wCell}
    {mc : ProbComp (Data r × ℕ)} (hexec : ExecRand w c (L.unpack argRegs m) mc)
    {z : Data r × ℕ} (hz : z ∈ mc.support) :
    z.2 + 1 ≤ autoRandFuel L c argRegs := by
  have hex : ∃ mc' : ProbComp (Data r × ℕ), ExecRand w c (L.unpack argRegs m) mc' := ⟨mc, hexec⟩
  refine le_trans ?_ (Finset.le_sup (Finset.mem_univ m))
  rw [dite_eq_left hex, (Classical.choose_spec hex).unique hexec]
  exact Nat.add_le_add_right (snd_le_probCompMaxSnd mc hz) 1

/-- Exact finite-tree `ExecRand` simulation over an arbitrary `RegLayout`: reproduces the **exact**
`(output, postMem)` distribution of `mc` with **zero** `η` slack and expected probes bounded by
`(ProbComp.expect mc fun z => (z.2 : ℝ≥0∞)) + L.overhead`. -/
theorem simExecRandLayout {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {mc : ProbComp (Data r × ℕ)} (hexec : ExecRand w c (L.unpack argRegs m) mc) :
    let tree := simProgRand (w := w) L (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns (autoRandFuel L c argRegs)
    (tree.run m).map Prod.fst =
        mc.eval.map (fun z => ((decode z.1.regs).getD defaultAns, L.pack z.1)) ∧
      tree.expectedProbes m ≤
        ProbComp.expect mc (fun z => (z.2 : ℝ≥0∞)) + (L.overhead : ℝ≥0∞) := by
  intro tree
  set K := autoRandFuel L c argRegs
  set x₀ := L.unpack argRegs m
  have heval : evalRand w (c.program retReg) K ⟨0, x₀⟩ =
      mc.eval.map fun z => RandCfg.halted (z.1.regs retReg) z.1 := by
    rw [evalRand, hexec.runRand_program retReg fun z hz => le_autoRandFuel_of_execRand L hexec hz,
      ProbComp.eval_map]
  have hp_run_zero :
      (evalRand w (c.program retReg) K ⟨0, x₀⟩).toOuterMeasure (RandCfg.runningSet r) = 0 := by
    simp [heval, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  have hcdist : ExecCodeDist w c x₀ (mc.eval.map Prod.fst)
      (ProbComp.expect mc fun z => (z.2 : ℝ≥0∞)) := by
    simpa [ProbComp.eval_map] using ExecCodeDist.of_execRand hexec
  have hpdist := execProgramDist_of_execCodeDist hcdist retReg
  obtain ⟨_, hexp_sim, -⟩ :=
    simProgRand_lasVegas_spec L (c.program retReg) argRegs (fun _ regs => decode regs)
      defaultAns K hm harg hpdist
  rw [hp_run_zero, zero_mul, add_zero] at hexp_sim
  refine ⟨?_, hexp_sim.trans (add_le_add
    (continuing_sum_le_of_almostSurelyHalts hpdist.almostSurelyHalts hpdist.1 K) le_rfl)⟩
  rw [simProgRand_law L _ argRegs _ defaultAns K hm harg, heval, PMF.map_comp, PMF.map_comp]
  rfl

/-- Exact finite-tree `ExecRand` simulation in standard `w`-bit layout (`S + persCount input` cells
of width `w`, additive overhead `2 * persCount input`). -/
theorem simExecRand {B : Basis} {r S w : ℕ} {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + persCount input) w)
    {mc : ProbComp (Data r × ℕ)}
    (hexec : ExecRand w c (unpackData input argRegs base S w m) mc) :
    let L := standardLayout input base S w
    let tree := simProgRand (w := w) L (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns (autoRandFuel L c argRegs)
    (tree.run m).map Prod.fst =
        mc.eval.map (fun z => ((decode z.1.regs).getD defaultAns, packMem input base S w z.1)) ∧
      tree.expectedProbes m ≤
        ProbComp.expect mc (fun z => (z.2 : ℝ≥0∞)) + (2 * persCount input : ℕ) :=
  standardLayout_overhead input base S w ▸ simExecRandLayout (standardLayout input base S w)
    c retReg argRegs decode defaultAns trivial harg hexec

/-- Exact finite-tree `ExecRand` simulation in wide-cell single-spill layout (`S + 1` cells of width
`wideWidth input w`, additive overhead `if persCount input = 0 then 0 else 2 ≤ 2`). -/
theorem simExecRandWide {B : Basis} {r S w : ℕ} {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {m : Mem (S + 1) (wideWidth input w)}
    (hm : (wideLayout input base S w).ValidMem m)
    {mc : ProbComp (Data r × ℕ)}
    (hexec : ExecRand w c (unpackDataWide input argRegs base S w m) mc) :
    let L := wideLayout input base S w
    let tree := simProgRand (w := w) L (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns (autoRandFuel L c argRegs)
    (tree.run m).map Prod.fst =
        mc.eval.map (fun z =>
          ((decode z.1.regs).getD defaultAns, packMemWide input base S w z.1)) ∧
      tree.expectedProbes m ≤
        ProbComp.expect mc (fun z => (z.2 : ℝ≥0∞)) +
          ((if persCount input = 0 then 0 else 2 : ℕ) : ℝ≥0∞) :=
  wideLayout_overhead input base S w ▸ simExecRandLayout (wideLayout input base S w)
    c retReg argRegs decode defaultAns hm harg hexec

/-! #### Antitone tail decay and uniform finite-horizon cutoff selection -/

/-- Active-configuration probability `(evalRand w p K s).toOuterMeasure (RandCfg.runningSet r)` is
antitone in `K` because `.halted` and `.faulted` are absorbing. -/
theorem evalRand_runningSet_antitone {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (s : State r) :
    Antitone fun K => (evalRand w p K s).toOuterMeasure (RandCfg.runningSet r) := by
  refine antitone_nat_of_succ_le fun K => ?_
  rw [evalRand_succ_right, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine tsum_le_tsum fun cfg => ?_
  cases cfg with
  | running u =>
    simpa using mul_le_mul' (le_refl (evalRand w p K s (.running u)))
      (Probability.PMF.toOuterMeasure_le_one _ _)
  | halted v d => simp [stepRand_halted, PMF.toOuterMeasure_pure_apply]
  | faulted => simp [stepRand_faulted, PMF.toOuterMeasure_pure_apply]

/-- For any antitone sequence `a : ℕ → ℝ≥0∞` with `∑' t, a t ≠ ⊤`, `(A + B * K) * a K → 0` as
`K → ∞`. -/
theorem exists_cutoff_mul_le {a : ℕ → ℝ≥0∞} (ha : Antitone a) (hsum : (∑' t, a t) ≠ ⊤)
    (A B : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K ≥ K₀, a K * ((A : ℝ≥0∞) + (B : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η := by
  set C : ℕ := max B 1
  have hC_ne_top : ((3 * C : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top (3 * C)
  -- The tail sums of a summable sequence tend to `0`, so some tail is below `η / (3 * C)`.
  obtain ⟨N, hN⟩ := ((ENNReal.tendsto_sum_nat_add a hsum).eventually
    (gt_mem_nhds (ENNReal.div_pos hη.ne' hC_ne_top))).exists
  refine ⟨max 1 (2 * N + A + 2), le_max_left _ _, fun K hK => ?_⟩
  have hK_ge : 2 * N + A + 2 ≤ K := (le_max_right 1 _).trans hK
  set M : ℕ := K - N
  have hM_mul_le : (M : ℝ≥0∞) * a K ≤ η / ((3 * C : ℕ) : ℝ≥0∞) :=
    calc (M : ℝ≥0∞) * a K = ∑ _i ∈ Finset.range M, a K := by simp
      _ ≤ ∑ i ∈ Finset.range M, a (i + N) :=
          Finset.sum_le_sum fun i hi => ha (by have := Finset.mem_range.mp hi; omega)
      _ ≤ ∑' k, a (k + N) := sum_le_tsum _
      _ ≤ _ := hN.le
  have hnat : A + B * K ≤ 3 * C * M :=
    calc A + B * K ≤ C * M + C * (2 * M) := Nat.add_le_add
          ((show A ≤ M by omega).trans (Nat.le_mul_of_pos_left M (lt_max_of_lt_right Nat.one_pos)))
          (Nat.mul_le_mul (le_max_left B 1) (by omega))
      _ = 3 * C * M := by ring
  calc a K * ((A : ℝ≥0∞) + (B : ℝ≥0∞) * (K : ℝ≥0∞))
    _ ≤ a K * (((3 * C : ℕ) : ℝ≥0∞) * (M : ℝ≥0∞)) := mul_le_mul' le_rfl (mod_cast hnat)
    _ = ((3 * C : ℕ) : ℝ≥0∞) * ((M : ℝ≥0∞) * a K) := by ac_rfl
    _ ≤ ((3 * C : ℕ) : ℝ≥0∞) * (η / ((3 * C : ℕ) : ℝ≥0∞)) := mul_le_mul' le_rfl hM_mul_le
    _ ≤ η := ENNReal.mul_div_le

/-- Uniform finite-horizon cutoff selection across a finite operation alphabet `opsAlphabet` and the
finite memory space `Mem (S + regCells) wCell`: produces a single `K ≥ 1` such that for every
`o ∈ opsAlphabet` and `m` satisfying `Good o m`, the active-tail product
`p_run(K, o, m) * (A + B * K)` is at most `η`. -/
theorem exists_uniform_cutoff {Op : Type*} {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ}
    (L : RegLayout r input base S w regCells wCell)
    (opsAlphabet : Finset Op) (Good : Op → Mem (S + regCells) wCell → Prop)
    (prog : Op → Program B r) (argRegs : Op → Fin r → ℕ)
    (hfin : ∀ o ∈ opsAlphabet, ∀ m, Good o m →
      expectedTime w (prog o) ⟨0, L.unpack (argRegs o) m⟩ ≠ ⊤)
    (A B : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ o ∈ opsAlphabet, ∀ m, Good o m →
      (evalRand w (prog o) K ⟨0, L.unpack (argRegs o) m⟩).toOuterMeasure (RandCfg.runningSet r) *
        ((A : ℝ≥0∞) + (B : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η := by
  choose! kPair _ hk using fun (o : Op) (m : Mem (S + regCells) wCell) (ho : o ∈ opsAlphabet)
      (hg : Good o m) =>
    exists_cutoff_mul_le (evalRand_runningSet_antitone w (prog o) ⟨0, L.unpack (argRegs o) m⟩)
      (hfin o ho m hg) A B hη
  refine ⟨max 1 ((opsAlphabet ×ˢ Finset.univ).sup fun om => kPair om.1 om.2), le_max_left _ _,
    fun o ho m hgood => hk o m ho hgood _ ?_⟩
  exact (Finset.le_sup (f := fun om : Op × Mem (S + regCells) wCell => kPair om.1 om.2)
    (b := (o, m)) (Finset.mem_product.mpr ⟨ho, Finset.mem_univ m⟩)).trans (le_max_right 1 _)

end Cslib.CellProbe
