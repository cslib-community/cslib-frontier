/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.NatClog
public import CslibFrontier.Computability.WordRAM.MemoryWindow.Normalization
public import CslibFrontier.Computability.WordRAM.Power
public import CslibFrontier.Computability.WordRAM.Width
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.Power.Rename
import CslibFrontier.Computability.WordRAM.RegisterFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Dynamic virtual-width memory-window adapters

`MemoryWindow.compile` translates a width-independent `r`-register program to run inside a
caller-owned physical memory interval `[b, b + 2 ^ w₀)` when `Reg.base` holds `b` and
`Reg.modulus` holds `2 ^ w₀`. When a caller invokes that translated routine at an unknown physical
word width `W ≥ w₀`, it computes the virtual modulus `2 ^ w₀` at runtime from an input-derived
scalar size `S` (`2 ≤ S`) without reading `W`:

1. `NatClog.program` computes `⌈log₂ S⌉` in `5 ⌈log₂ S⌉ + 5` instructions;
2. `modulusArgs` multiplies `⌈log₂ S⌉` by the fixed constant `widthCoeff` to form
   `w₀ = widthCoeff * ⌈log₂ S⌉` and loads base `2` in `3` instructions;
3. `Power.program` computes `2 ^ w₀` in `4 w₀ + 5` instructions;
4. `MemoryWindow.normalizeRegisters` reduces all `r` source registers modulo `2 ^ w₀` in `r + 1`
   instructions without clearing the caller's dirty memory window;
5. `MemoryWindow.compile callee` executes the translated callee in `3 * T` instructions, clipping
   dirty loads modulo `2 ^ w₀` and preserving all memory outside `[b, b + 2 ^ w₀)`.

This module provides both the in-place `Data (r + 3)` setup (`dynamicSetup`, where five low source
registers serve as temporary scratch before register normalization) and the embedded-bank adapter
(`dynamicSetupBank` and `dynamicCallBank`, where the window bank `Fin (r + 3) → Fin R` and five
scratch registers `Fin 5 → Fin R` sit inside a larger caller register file `Data R`).

## Main definitions

* `Cslib.WordRAM.MemoryWindow.dynamicWidth`, `Cslib.WordRAM.MemoryWindow.dynamicWindowSize`:
  virtual source width `widthCoeff * Nat.clog 2 S` and window size `2 ^ dynamicWidth widthCoeff S`.
* `Cslib.WordRAM.MemoryWindow.modulusArgs`, `Cslib.WordRAM.MemoryWindow.withDynamicModulus`:
  runtime computation of `2 ^ (widthCoeff * Nat.clog 2 S)` in a 5-register scratch bank.
* `Cslib.WordRAM.MemoryWindow.dynamicSetup`: in-place modulus computation and source-register
  normalization on `Data (r + 3)`.
* `Cslib.WordRAM.MemoryWindow.dynamicSetupBank`, `Cslib.WordRAM.MemoryWindow.dynamicCallBank`:
  embedded-bank dynamic window setup and complete setup-plus-callee execution on `Data R`.

## Main results

* `Cslib.WordRAM.MemoryWindow.dynamicWindowSize_bounds`,
  `Cslib.WordRAM.MemoryWindow.dynamicWidth_fits`: parameter and physical-width fit bounds from
  `Fits W (b + 4 * dynamicWindowSize widthCoeff S)`.
* `Cslib.WordRAM.MemoryWindow.exec_withDynamicModulus`: runtime modulus computation in
  `(4 * widthCoeff + 5) * Nat.clog 2 S + 13` instructions.
* `Cslib.WordRAM.MemoryWindow.exec_dynamicSetup`,
  `Cslib.WordRAM.MemoryWindow.size_dynamicSetup`,
  `Cslib.WordRAM.MemoryWindow.dynamicSetup_not_readsWidth`: execution, code size, and width
  blindness of in-place setup.
* `Cslib.WordRAM.MemoryWindow.exec_dynamicSetupBank`,
  `Cslib.WordRAM.MemoryWindow.size_dynamicSetupBank`,
  `Cslib.WordRAM.MemoryWindow.dynamicSetupBank_not_readsWidth`,
  `Cslib.WordRAM.MemoryWindow.preserves_dynamicSetupBank`: execution, code size, width blindness,
  and register preservation of embedded-bank setup.
* `Cslib.WordRAM.MemoryWindow.exec_dynamicCallBank`,
  `Cslib.WordRAM.MemoryWindow.size_dynamicCallBank`,
  `Cslib.WordRAM.MemoryWindow.dynamicCallBank_not_readsWidth`,
  `Cslib.WordRAM.MemoryWindow.preserves_dynamicCallBank`: complete dynamic-window call properties.
* `Cslib.WordRAM.MemoryWindow.view_mem_init_of_inputFits`: source-view memory agreement on an
  initialized input prefix admitted at the source width.
-/

public section

namespace Cslib.WordRAM.MemoryWindow

open Cslib.Algorithms.WordRAM

/-- Virtual source width `widthCoeff * ⌈log₂ S⌉` computed from a runtime scalar size `S`. -/
@[expose] def dynamicWidth (widthCoeff S : ℕ) : ℕ :=
  widthCoeff * Nat.clog 2 S

/-- Virtual address-space reservation `2 ^ (widthCoeff * ⌈log₂ S⌉)`. -/
@[expose] def dynamicWindowSize (widthCoeff S : ℕ) : ℕ :=
  2 ^ dynamicWidth widthCoeff S

/-- For `1 ≤ widthCoeff` and `2 ≤ S`, the dynamic window covers `S`, strictly exceeds its
exponent `dynamicWidth widthCoeff S`, and strictly exceeds `widthCoeff`. -/
theorem dynamicWindowSize_bounds {widthCoeff S : ℕ} (hc : 1 ≤ widthCoeff) (hS : 2 ≤ S) :
    S ≤ dynamicWindowSize widthCoeff S ∧
      dynamicWidth widthCoeff S < dynamicWindowSize widthCoeff S ∧
      widthCoeff < dynamicWindowSize widthCoeff S := by
  have hlog : Nat.clog 2 S ≤ dynamicWidth widthCoeff S := Nat.le_mul_of_pos_left _ hc
  exact ⟨(Nat.le_pow_clog Nat.one_lt_two S).trans (Nat.pow_le_pow_right Nat.zero_lt_two hlog),
    Nat.lt_two_pow_self,
    (Nat.le_mul_of_pos_right _ (Nat.clog_pos Nat.one_lt_two (by omega))).trans_lt
      Nat.lt_two_pow_self⟩

/-- When `b + 4 * dynamicWindowSize widthCoeff S` fits in physical width `W` (with
`1 ≤ widthCoeff` and `2 ≤ S`), `dynamicWidth widthCoeff S + 2 ≤ W`, the window endpoint
`b + dynamicWindowSize widthCoeff S` fits in `W`, and `dynamicWindowSize_bounds` holds. -/
theorem dynamicWidth_fits {W b widthCoeff S : ℕ} (hc : 1 ≤ widthCoeff) (hS : 2 ≤ S)
    (hfit : Fits W (b + 4 * dynamicWindowSize widthCoeff S)) :
    dynamicWidth widthCoeff S + 2 ≤ W ∧
      dynamicWidth widthCoeff S ≤ W ∧
      Fits W (b + dynamicWindowSize widthCoeff S) ∧
      S ≤ dynamicWindowSize widthCoeff S ∧
      dynamicWidth widthCoeff S < dynamicWindowSize widthCoeff S ∧
      widthCoeff < dynamicWindowSize widthCoeff S := by
  obtain ⟨hSle, hwlt, hclt⟩ := dynamicWindowSize_bounds hc hS
  have hpow : 2 ^ (dynamicWidth widthCoeff S + 2) ≤ b + 4 * dynamicWindowSize widthCoeff S := by
    simp only [dynamicWindowSize, pow_add, Nat.reducePow]
    omega
  have hw2 : dynamicWidth widthCoeff S + 2 ≤ W := (hfit.lt_of_pow_le hpow).le
  exact ⟨hw2, by omega, hfit.of_le (by omega), hSle, hwlt, hclt⟩

/-- Multiply `⌈log₂ S⌉` in `scratch 1` by `widthCoeff` into `scratch 3` and load base `2` into
`scratch 2` for `Power.program`. -/
@[expose] def modulusArgs {R : ℕ} (scratch : Fin 5 → Fin R) (widthCoeff : ℕ) :
    Code .standard R :=
  let r1 := scratch 1
  let r2 := scratch 2
  let r3 := scratch 3
  ram[ r2 ← #widthCoeff; r3 ← r1 * r2; r2 ← #2 ]

/-- From `S` in `scratch 0`, compute `2 ^ (widthCoeff * Nat.clog 2 S)` into `scratch 0` using
`NatClog.program` and `Power.program`, then execute `cont`. -/
@[expose] def withDynamicModulus {R : ℕ} (scratch : Fin 5 → Fin R) (widthCoeff : ℕ)
    (cont : Code .standard R) : Code .standard R :=
  .seq (NatClog.program.rename (fun i => scratch (i.castAdd 1))) <|
    .seq (modulusArgs scratch widthCoeff) <|
      .seq (Power.program.rename scratch) cont

/-- Computing the dynamic modulus prepends exactly `20` assembled instructions to `cont`. -/
theorem size_withDynamicModulus {R : ℕ} (scratch : Fin 5 → Fin R) (widthCoeff : ℕ)
    (cont : Code .standard R) :
    (withDynamicModulus scratch widthCoeff cont).size = 20 + cont.size := by
  simp only [withDynamicModulus, Code.size, Code.size_rename]
  change 9 + (3 + (8 + cont.size)) = 20 + cont.size
  omega

/-- Dynamic modulus computation reads the physical width if and only if `cont` does. -/
theorem readsWidth_withDynamicModulus {R : ℕ} (scratch : Fin 5 → Fin R) (widthCoeff : ℕ)
    (cont : Code .standard R) :
    (withDynamicModulus scratch widthCoeff cont).ReadsWidth ↔ cont.ReadsWidth := by
  have hclog : ¬NatClog.program.ReadsWidth := by decide
  have hargs : ¬(modulusArgs scratch widthCoeff).ReadsWidth :=
    not_or.mpr ⟨nofun, not_or.mpr ⟨Op.readsWidth_bin _ _ _ _, nofun⟩⟩
  have hpow : ¬Power.program.ReadsWidth := by decide
  simp only [withDynamicModulus, Code.ReadsWidth, Code.readsWidth_rename,
    hclog, hargs, hpow, false_or]

/-- Dynamic modulus computation preserves every register outside `scratch` that `cont` preserves. -/
theorem preserves_withDynamicModulus {R : ℕ} (scratch : Fin 5 → Fin R) (widthCoeff : ℕ)
    {cont : Code .standard R} {i : Fin R}
    (hscratch : ∀ k : Fin 5, scratch k ≠ i) (hcont : cont.Preserves i) :
    (withDynamicModulus scratch widthCoeff cont).Preserves i := by
  refine ⟨NatClog.program.preserves_rename_of_forall_ne _ i (fun j => hscratch (j.castAdd 1)),
    ⟨?_, ?_, ?_⟩, Power.program.preserves_rename_of_forall_ne scratch i hscratch, hcont⟩
  · simp [Code.Preserves, Op.dest, hscratch 2]
  · simp [Code.Preserves, hscratch 3]
  · simp [Code.Preserves, Op.dest, hscratch 2]

/-- Execute `NatClog.program`, multiply by `widthCoeff`, and run `Power.program` in `scratch`,
delivering `dynamicWindowSize widthCoeff S` in `scratch 0` with unchanged memory and external
registers to `cont`. -/
theorem exec_withDynamicModulus {R W widthCoeff S tCont : ℕ}
    {scratch : Fin 5 → Fin R} (hscratch : Function.Injective scratch)
    (hc : 1 ≤ widthCoeff) (hS : 2 ≤ S)
    {cont : Code .standard R} {x : Data R} {Q : Data R → Prop}
    (hxS : x.regs (scratch 0) = S)
    (hfit : Fits W (4 * dynamicWindowSize widthCoeff S))
    (hcont : ∀ z : Data R, z.mem = x.mem →
      z.regs (scratch 0) = dynamicWindowSize widthCoeff S →
      (∀ i : Fin R, (∀ k : Fin 5, scratch k ≠ i) → z.regs i = x.regs i) →
      ∃ y, ExecWithin W cont z y tCont ∧ Q y) :
    ∃ y, ExecWithin W (withDynamicModulus scratch widthCoeff cont) x y
        ((4 * widthCoeff + 5) * Nat.clog 2 S + 13 + tCont) ∧ Q y := by
  obtain ⟨-, -, -, hSle, hwlt, hclt⟩ :=
    dynamicWidth_fits hc hS ((Nat.zero_add (4 * dynamicWindowSize widthCoeff S)).symm ▸ hfit)
  have hlog_le : Nat.clog 2 S ≤ dynamicWidth widthCoeff S := Nat.le_mul_of_pos_left _ hc
  have hwin_ge2 : 2 ≤ dynamicWindowSize widthCoeff S := hS.trans hSle
  have h2 : Fits W 2 := hfit.of_le (by omega)
  have hc_fit : Fits W widthCoeff := hfit.of_le (by omega)
  have hS1 : Fits W (S + 1) := hfit.of_le (by omega)
  have hlog1 : Fits W (Nat.clog 2 S + 1) := hfit.of_le (by omega)
  have hexp : Fits W (Nat.clog 2 S * widthCoeff) := hfit.of_le (by
    have hmul : Nat.clog 2 S * widthCoeff = dynamicWidth widthCoeff S := Nat.mul_comm _ _
    omega)
  have hpfit : Fits W (2 ^ dynamicWidth widthCoeff S + dynamicWidth widthCoeff S + 2) :=
    hfit.of_le (by change dynamicWindowSize widthCoeff S + _ + 2 ≤ _; omega)
  let clogScratch : Fin 4 → Fin R := fun i => scratch (i.castAdd 1)
  have hclog_inj : Function.Injective clogScratch :=
    hscratch.comp (Fin.castAdd_injective 4 1)
  have harg0 : (x.comap clogScratch).regs NatClog.arg = S := hxS
  obtain ⟨l, hl, ⟨hl_res, hl_mem, -, -⟩, hl_frame⟩ :=
    ExecWithin.rename_post hclog_inj (NatClog.exec (x.comap clogScratch) h2
      (by simpa only [harg0] using hS1) (by simpa only [harg0] using hlog1))
  have hl' : ExecWithin W (NatClog.program.rename clogScratch) x l (5 * Nat.clog 2 S + 5) := by
    simpa only [harg0] using hl
  have hl_val : l.regs (scratch 1) = Nat.clog 2 S := hxS ▸ hl_res
  have h12 : scratch 1 ≠ scratch 2 := hscratch.ne (by decide)
  have h32 : scratch 3 ≠ scratch 2 := hscratch.ne (by decide)
  refine WP.exists_execWithin ?_
  dsimp only [withDynamicModulus, modulusArgs]
  refine WP.seq (WP.of_execWithin hl' ?_)
  wram_exec [hl_val]
  refine WP.name fun a ha => ?_
  obtain ⟨z, hz, hz_val, -, -, hz_mem, -, -, hz_frame⟩ :=
    Power.exec_rename scratch hscratch 2 (dynamicWidth widthCoeff S) (by decide) a
      (by wram_simp [ha, Power.base]) (by wram_simp [ha, Power.exponent]; exact Nat.mul_comm _ _)
      hpfit
  refine WP.of_execWithin hz ?_
  obtain ⟨y, hy, hQ⟩ := hcont z (by rw [hz_mem, ha]; exact hl_mem) hz_val fun i hi => by
    have := (hi 2).symm
    have := (hi 3).symm
    rw [hz_frame i hi, ha]; wram_simp [hl_frame i fun j => hi (j.castAdd 1)]
  refine WP.of_execWithin hy ⟨?_, hQ⟩
  dsimp only [dynamicWidth]
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

/-- Compute `2 ^ (widthCoeff * Nat.clog 2 S)` from `S` in `scratch 0`, store it in `Reg.modulus`,
and normalize all `r` source registers modulo `2 ^ (widthCoeff * Nat.clog 2 S)`. -/
@[expose] def dynamicSetup {r : ℕ} (scratch : Fin 5 → Fin (r + 3)) (widthCoeff : ℕ) :
    Code .standard (r + 3) :=
  withDynamicModulus scratch widthCoeff <|
    .seq (.op (.copy Reg.modulus (scratch 0))) (normalizeRegisters r)

/-- Code size of `dynamicSetup`. -/
theorem size_dynamicSetup {r : ℕ} (scratch : Fin 5 → Fin (r + 3)) (widthCoeff : ℕ) :
    (dynamicSetup scratch widthCoeff).size = r + 22 := by
  simp only [dynamicSetup, size_withDynamicModulus, Code.size, size_normalizeRegisters]
  omega

/-- `dynamicSetup` never reads the physical word width. -/
theorem dynamicSetup_not_readsWidth {r : ℕ} (scratch : Fin 5 → Fin (r + 3)) (widthCoeff : ℕ) :
    ¬(dynamicSetup scratch widthCoeff).ReadsWidth := by
  rw [dynamicSetup, readsWidth_withDynamicModulus]
  simp only [Code.ReadsWidth, Op.ReadsWidth, normalizeRegisters_not_readsWidth, or_self,
    not_false_eq_true]

private theorem base_ne_modulus {r : ℕ} : (Reg.base : Fin (r + 3)) ≠ Reg.modulus := by
  simp [Fin.ext_iff, Reg.base, Reg.modulus]

/-- Execute `dynamicSetup` on `Data (r + 3)` when `Reg.base` holds `b` and `scratch 0` holds `S`.
All memory words survive and the resulting source view is bounded at `dynamicWidth widthCoeff S`. -/
theorem exec_dynamicSetup {r W b widthCoeff S : ℕ}
    {scratch : Fin 5 → Fin (r + 3)} (hscratch : Function.Injective scratch)
    (hbase : ∀ k : Fin 5, scratch k ≠ Reg.base)
    (hc : 1 ≤ widthCoeff) (hS : 2 ≤ S)
    (x : Data (r + 3)) (hb : x.regs Reg.base = b) (hxS : x.regs (scratch 0) = S)
    (hfit : Fits W (b + 4 * dynamicWindowSize widthCoeff S)) :
    ∃ y, ExecWithin W (dynamicSetup scratch widthCoeff) x y
        ((4 * widthCoeff + 5) * Nat.clog 2 S + r + 15) ∧
      y.mem = x.mem ∧
      Matches (dynamicWidth widthCoeff S) b (view (dynamicWidth widthCoeff S) b y) y ∧
      (view (dynamicWidth widthCoeff S) b y).Bounded (dynamicWidth widthCoeff S) := by
  obtain ⟨-, hw, -, -, -, -⟩ := dynamicWidth_fits hc hS hfit
  obtain ⟨y, hy, hpost⟩ := exec_withDynamicModulus hscratch hc hS hxS
    (hfit.of_le (by omega))
    (cont := .seq (.op (.copy Reg.modulus (scratch 0))) (normalizeRegisters r))
    (tCont := 1 + (r + 1))
    (Q := fun y => y.mem = x.mem ∧
      Matches (dynamicWidth widthCoeff S) b (view (dynamicWidth widthCoeff S) b y) y ∧
      (view (dynamicWidth widthCoeff S) b y).Bounded (dynamicWidth widthCoeff S))
    fun z hz_mem hz_val hz_frame => by
      have hzb : z.regs Reg.base = b := (hz_frame Reg.base hbase).trans hb
      have hbm := base_ne_modulus (r := r)
      refine WP.exists_execWithin ?_
      wram_exec [hz_val]
      refine WP.name fun z' hz' => ?_
      obtain ⟨y, hnorm, hymem, hymatch, hybound, -⟩ := exec_normalizeRegisters (b := b) z'
        (by wram_simp [hz', hzb]) (by wram_simp [hz', dynamicWindowSize]) hw
      exact WP.of_execWithin hnorm ⟨by omega, by rw [hymem, hz']; exact hz_mem, hymatch, hybound⟩
  exact ⟨y, hy.mono (by omega), hpost⟩

/-- Compute `2 ^ (widthCoeff * Nat.clog 2 S)` in `scratch`, copy `baseReg` and the computed
modulus into `winBank`, and normalize the `r` embedded source registers. -/
@[expose] def dynamicSetupBank {r R : ℕ} (winBank : Fin (r + 3) → Fin R)
    (scratch : Fin 5 → Fin R) (baseReg : Fin R) (widthCoeff : ℕ) : Code .standard R :=
  let wb := winBank Reg.base
  let wm := winBank Reg.modulus
  let s0 := scratch 0
  withDynamicModulus scratch widthCoeff <|
    .seq (ram[ wb ← baseReg; wm ← s0 ])
      ((normalizeRegisters r).rename winBank)

/-- Code size of `dynamicSetupBank`. -/
theorem size_dynamicSetupBank {r R : ℕ} (winBank : Fin (r + 3) → Fin R)
    (scratch : Fin 5 → Fin R) (baseReg : Fin R) (widthCoeff : ℕ) :
    (dynamicSetupBank winBank scratch baseReg widthCoeff).size = r + 23 := by
  simp only [dynamicSetupBank, size_withDynamicModulus, Code.size, Code.size_rename,
    size_normalizeRegisters]
  omega

/-- `dynamicSetupBank` never reads the physical word width. -/
theorem dynamicSetupBank_not_readsWidth {r R : ℕ} (winBank : Fin (r + 3) → Fin R)
    (scratch : Fin 5 → Fin R) (baseReg : Fin R) (widthCoeff : ℕ) :
    ¬(dynamicSetupBank winBank scratch baseReg widthCoeff).ReadsWidth := by
  rw [dynamicSetupBank, readsWidth_withDynamicModulus]
  simp only [Code.ReadsWidth, Op.ReadsWidth, Code.readsWidth_rename,
    normalizeRegisters_not_readsWidth, or_self, not_false_eq_true]

/-- `dynamicSetupBank` preserves every register outside `scratch` and `winBank`. -/
theorem preserves_dynamicSetupBank {r R : ℕ} (winBank : Fin (r + 3) → Fin R)
    (scratch : Fin 5 → Fin R) (baseReg : Fin R) (widthCoeff : ℕ) {i : Fin R}
    (hscratch : ∀ k : Fin 5, scratch k ≠ i)
    (hwin : ∀ j : Fin (r + 3), winBank j ≠ i) :
    (dynamicSetupBank winBank scratch baseReg widthCoeff).Preserves i := by
  apply preserves_withDynamicModulus scratch widthCoeff hscratch
  refine ⟨⟨?_, ?_⟩, (normalizeRegisters r).preserves_rename_of_forall_ne winBank i hwin⟩
  · simp [Code.Preserves, Op.dest, hwin Reg.base]
  · simp [Code.Preserves, Op.dest, hwin Reg.modulus]

/-- Execute `dynamicSetupBank` on `Data R` when `baseReg` holds `b` and `scratch 0` holds `S`.
All memory words and all registers outside `scratch` and `winBank` are preserved, and the
embedded window bank holds normalized source registers with modulus
`dynamicWindowSize widthCoeff S`. -/
theorem exec_dynamicSetupBank {r R W b widthCoeff S : ℕ}
    {winBank : Fin (r + 3) → Fin R} (hwin : Function.Injective winBank)
    {scratch : Fin 5 → Fin R} (hscratch : Function.Injective scratch)
    {baseReg : Fin R} (hbase : ∀ k : Fin 5, scratch k ≠ baseReg)
    (hmod : winBank Reg.base ≠ scratch 0)
    (hc : 1 ≤ widthCoeff) (hS : 2 ≤ S)
    (x : Data R) (hb : x.regs baseReg = b) (hxS : x.regs (scratch 0) = S)
    (hfit : Fits W (b + 4 * dynamicWindowSize widthCoeff S)) :
    ∃ y, ExecWithin W (dynamicSetupBank winBank scratch baseReg widthCoeff) x y
        ((4 * widthCoeff + 5) * Nat.clog 2 S + r + 16) ∧
      y.mem = x.mem ∧
      Matches (dynamicWidth widthCoeff S) b
        (view (dynamicWidth widthCoeff S) b (y.comap winBank)) (y.comap winBank) ∧
      (view (dynamicWidth widthCoeff S) b (y.comap winBank)).Bounded
        (dynamicWidth widthCoeff S) ∧
      ∀ i : Fin R, (∀ k : Fin 5, scratch k ≠ i) → (∀ j : Fin (r + 3), winBank j ≠ i) →
        y.regs i = x.regs i := by
  obtain ⟨-, hw, -, -, -, -⟩ := dynamicWidth_fits hc hS hfit
  let wb := winBank Reg.base
  let wm := winBank Reg.modulus
  let s0 := scratch 0
  obtain ⟨y, hy, hpost⟩ := exec_withDynamicModulus hscratch hc hS hxS
    (hfit.of_le (by omega))
    (cont := .seq (ram[ wb ← baseReg; wm ← s0 ])
      ((normalizeRegisters r).rename winBank))
    (tCont := 2 + (r + 1))
    (Q := fun y => y.mem = x.mem ∧
      Matches (dynamicWidth widthCoeff S) b
        (view (dynamicWidth widthCoeff S) b (y.comap winBank)) (y.comap winBank) ∧
      (view (dynamicWidth widthCoeff S) b (y.comap winBank)).Bounded
        (dynamicWidth widthCoeff S) ∧
      ∀ i : Fin R, (∀ k : Fin 5, scratch k ≠ i) → (∀ j : Fin (r + 3), winBank j ≠ i) →
        y.regs i = x.regs i)
    fun z hz_mem hz_val hz_frame => by
      have hzb : z.regs baseReg = b := (hz_frame baseReg hbase).trans hb
      have hbm := hwin.ne (base_ne_modulus (r := r))
      have hmod' := hmod.symm
      refine WP.exists_execWithin ?_
      wram_exec [hzb, hz_val]
      refine WP.name fun z₂ hz₂ => ?_
      obtain ⟨y, hnorm, ⟨hymem, hymatch, hybound, -⟩, hyframe⟩ :=
        ExecWithin.rename_post hwin (exec_normalizeRegisters (z₂.comap winBank)
          (show z₂.regs wb = b by wram_simp [hz₂])
          (show z₂.regs wm = _ by wram_simp [hz₂]; exact hz_val) hw)
      refine WP.of_execWithin hnorm ⟨by omega, hymem.trans (by rw [hz₂]; exact hz_mem),
        hymatch, hybound, fun i hi_s hi_w => ?_⟩
      have := (hi_w Reg.base).symm
      have := (hi_w Reg.modulus).symm
      rw [hyframe i hi_w, hz₂]
      wram_simp [hz_frame i hi_s]
  exact ⟨y, hy.mono (by omega), hpost⟩

/-- Complete dynamic-window call in an embedded bank: compute `2 ^ (widthCoeff * Nat.clog 2 S)` in
`scratch`, initialize `winBank` from `baseReg` and `scratch 0`, normalize the `r` source registers,
and execute `(MemoryWindow.compile callee).rename winBank`. -/
@[expose] def dynamicCallBank {r R : ℕ} (winBank : Fin (r + 3) → Fin R)
    (scratch : Fin 5 → Fin R) (baseReg : Fin R) (widthCoeff : ℕ)
    (callee : Code .standard r) : Code .standard R :=
  .seq (dynamicSetupBank winBank scratch baseReg widthCoeff)
    ((compile callee).rename winBank)

/-- Code-size bound for `dynamicCallBank`. -/
theorem size_dynamicCallBank {r R : ℕ} (winBank : Fin (r + 3) → Fin R)
    (scratch : Fin 5 → Fin R) (baseReg : Fin R) (widthCoeff : ℕ)
    (callee : Code .standard r) :
    (dynamicCallBank winBank scratch baseReg widthCoeff callee).size ≤
      r + 23 + 3 * callee.size := by
  have hc := size_compile callee
  simp only [dynamicCallBank, Code.size, size_dynamicSetupBank, Code.size_rename]
  omega

/-- `dynamicCallBank` never reads the physical word width when `callee` does not. -/
theorem dynamicCallBank_not_readsWidth {r R : ℕ} (winBank : Fin (r + 3) → Fin R)
    (scratch : Fin 5 → Fin R) (baseReg : Fin R) (widthCoeff : ℕ)
    {callee : Code .standard r} (hcallee : ¬callee.ReadsWidth) :
    ¬(dynamicCallBank winBank scratch baseReg widthCoeff callee).ReadsWidth := by
  simp only [dynamicCallBank, Code.ReadsWidth, dynamicSetupBank_not_readsWidth,
    Code.readsWidth_rename, readsWidth_compile, hcallee, or_self, not_false_eq_true]

/-- `dynamicCallBank` preserves every register outside `scratch` and `winBank`. -/
theorem preserves_dynamicCallBank {r R : ℕ} (winBank : Fin (r + 3) → Fin R)
    (scratch : Fin 5 → Fin R) (baseReg : Fin R) (widthCoeff : ℕ)
    (callee : Code .standard r) {i : Fin R}
    (hscratch : ∀ k : Fin 5, scratch k ≠ i)
    (hwin : ∀ j : Fin (r + 3), winBank j ≠ i) :
    (dynamicCallBank winBank scratch baseReg widthCoeff callee).Preserves i :=
  ⟨preserves_dynamicSetupBank winBank scratch baseReg widthCoeff hscratch hwin,
    (compile callee).preserves_rename_of_forall_ne winBank i hwin⟩

/-- Execute a width-independent `callee` in a dynamic virtual-width window `[b, b + 2 ^ w₀)`
(with `w₀ = dynamicWidth widthCoeff S`), preserving all memory outside `[b, b + 2 ^ w₀)` and all
registers outside `scratch` and `winBank`. -/
theorem exec_dynamicCallBank {r R W b widthCoeff S T : ℕ}
    {winBank : Fin (r + 3) → Fin R} (hwin : Function.Injective winBank)
    {scratch : Fin 5 → Fin R} (hscratch : Function.Injective scratch)
    {baseReg : Fin R} (hbase : ∀ k : Fin 5, scratch k ≠ baseReg)
    (hmod : winBank Reg.base ≠ scratch 0)
    (hc : 1 ≤ widthCoeff) (hS : 2 ≤ S)
    {callee : Code .standard r} (hcallee : ¬callee.ReadsWidth)
    (x : Data R) (hb : x.regs baseReg = b) (hxS : x.regs (scratch 0) = S)
    (hfit : Fits W (b + 4 * dynamicWindowSize widthCoeff S))
    {Post : Data r → Prop}
    (hsrc : ∀ v : Data r, v.Bounded (dynamicWidth widthCoeff S) →
      (∀ a, v.mem a = x.mem (b + a) % dynamicWindowSize widthCoeff S) →
      ∃ z, ExecWithin (dynamicWidth widthCoeff S) callee v z T ∧ Post z) :
    ∃ z : Data r, ∃ y : Data R,
      ExecWithin W (dynamicCallBank winBank scratch baseReg widthCoeff callee) x y
        ((4 * widthCoeff + 5) * Nat.clog 2 S + r + 16 + 3 * T) ∧
      Matches (dynamicWidth widthCoeff S) b z (y.comap winBank) ∧
      Post z ∧
      (∀ a, a < b ∨ b + dynamicWindowSize widthCoeff S ≤ a → y.mem a = x.mem a) ∧
      (∀ i : Fin R, (∀ k : Fin 5, scratch k ≠ i) → (∀ j : Fin (r + 3), winBank j ≠ i) →
        y.regs i = x.regs i) := by
  obtain ⟨-, hw, hwin_fit, -, -, -⟩ := dynamicWidth_fits hc hS hfit
  obtain ⟨s, hs, hsmem, hsmatch, hsbound, hsregs⟩ :=
    exec_dynamicSetupBank hwin hscratch hbase hmod hc hS x hb hxS hfit
  let v := view (dynamicWidth widthCoeff S) b (s.comap winBank)
  have hvmem (a : ℕ) : v.mem a = x.mem (b + a) % dynamicWindowSize widthCoeff S :=
    congrArg (· % _) (congrFun hsmem (b + a))
  obtain ⟨z, hz, hpost⟩ := hsrc v hsbound hvmem
  obtain ⟨y, hy, ⟨hymatch, hyframe_mem⟩, hyframe_regs⟩ :=
    ExecWithin.rename_post hwin
      (execWithin hz hcallee hsbound hsmatch hw hwin_fit)
  exact ⟨z, y, hs.seq hy, hymatch, hpost, fun a ha => (hyframe_mem a ha).trans (congrFun hsmem a),
    fun i hi_s hi_w => (hyframe_regs i hi_w).trans (hsregs i hi_s hi_w)⟩

/-- Whenever `inp` fits at width `w` and physical memory `[b, b + L)` equals `(Data.init inp).mem`,
the clipped source view `view w b x` agrees on `[0, L)` with `Data.init inp`. -/
theorem view_mem_init_of_inputFits {r r₀ w b L : ℕ} {inp : List ℕ} (hi : InputFits w inp)
    (x : Data (r + 3)) (hinput : ∀ q < L, x.mem (b + q) = (Data.init inp : Data r₀).mem q) :
    ∀ q < L, (view w b x).mem q = (Data.init inp : Data r₀).mem q := by
  have hbound := Data.Bounded.init (r := r₀) hi
  intro q hq
  change x.mem (b + q) % 2 ^ w = _
  rw [hinput q hq, Nat.mod_eq_of_lt (hbound.2 q)]

end Cslib.WordRAM.MemoryWindow
