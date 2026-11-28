/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

-- upstream: local-only (tests)

import CslibFrontier.Computability.WordRAM.Admission
import CslibFrontier.Computability.WordRAM.FlatEndpoint
import CslibFrontier.Computability.WordRAM.MemoryWindow.Dynamic
import CslibFrontier.Computability.WordRAM.Structured.FastEval
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Tests for `MemoryWindow.Dynamic` and `FlatEndpoint`

Exercises:
1. A width-blind 4-register callee (`pairSumCallee`) adapted to a caller-owned runtime window via
   `MemoryWindow.dynamicCallBank`, tolerating dirty physical words larger than `2 ^ w₀` and
   preserving caller registers and outside sentinel memory cells.
2. Packaging the complete initialized caller into a parametric `FlatEndpoint` over `ℕ × ℕ`,
   yielding wide-width `InputFits`, flat `Runs`, halting `Executes`, and physical-width-independent
   prefix envelopes across all `W ≥ wMin p`.
-/

set_option linter.hashCommand false

namespace CslibFrontierTests.WordRAMDynamicWindow

open Cslib.WordRAM

private abbrev cA : Fin 4 := 0
private abbrev cB : Fin 4 := 1
private abbrev cOut : Fin 4 := 2
private abbrev cAddr : Fin 4 := 3

/-- Width-blind 4-register callee: loads virtual cells `1` and `2`, adds them into `cOut`, and
stores the sum into virtual cell `3`. -/
private def pairSumCallee : Code .standard 4 := ram[
  cAddr ← #1; cA ← *cAddr;
  cAddr ← #2; cB ← *cAddr;
  cOut ← cA + cB;
  cAddr ← #3; *cAddr ← cOut ]

private theorem pairSumCallee_not_readsWidth : ¬pairSumCallee.ReadsWidth := by
  decide

private theorem exec_pairSumCallee {w : ℕ} (v : Data 4)
    (h3 : Fits w 3) (hsum : Fits w (v.mem 1 + v.mem 2)) :
    ∃ z : Data 4, ExecWithin w pairSumCallee v z 7 ∧
      z.regs cOut = v.mem 1 + v.mem 2 ∧ z.mem 3 = v.mem 1 + v.mem 2 := by
  have h1 : Fits w 1 := h3.of_le (by omega)
  have h2 : Fits w 2 := h3.of_le (by omega)
  refine ⟨?z, ?run, ?regOut, ?memOut⟩
  case run =>
    ram_eval [pairSumCallee, h1, h2, h3, hsum, cA, cB, cOut, cAddr, Fin.mk.injEq]
  case regOut => simp +decide [cOut]
  case memOut => simp +decide

-- Caller register layout on `Data 16`:
-- `0` = caller sentinel register, `1` = runtime base, `2..8` = window bank (4 + 3),
-- `9..13` = 5-register dynamic-modulus scratch bank, `14` = output register, `15` = temporary.
private abbrev rGuard : Fin 16 := 0
private abbrev rBase : Fin 16 := 1
private abbrev rOut : Fin 16 := 14
private abbrev rTmp : Fin 16 := 15

private def winBank (i : Fin 7) : Fin 16 := ⟨2 + i.val, by omega⟩
private def scratch (i : Fin 5) : Fin 16 := ⟨9 + i.val, by omega⟩

private theorem winBank_injective : Function.Injective winBank := fun i j h =>
  Fin.ext (by simpa only [winBank] using Nat.add_left_cancel (congrArg Fin.val h))

private theorem scratch_injective : Function.Injective scratch := fun i j h =>
  Fin.ext (by simpa only [scratch] using Nat.add_left_cancel (congrArg Fin.val h))

private def dynamicCall : Code .standard 16 :=
  MemoryWindow.dynamicCallBank winBank scratch rBase 2 pairSumCallee

-- Static properties proved symbolically via `MemoryWindow.Dynamic`.
example : ¬dynamicCall.ReadsWidth :=
  MemoryWindow.dynamicCallBank_not_readsWidth winBank scratch rBase 2
    pairSumCallee_not_readsWidth

example : dynamicCall.size ≤ 48 :=
  MemoryWindow.size_dynamicCallBank winBank scratch rBase 2 pairSumCallee

example : dynamicCall.Preserves rGuard :=
  MemoryWindow.preserves_dynamicCallBank winBank scratch rBase 2 pairSumCallee
    (by decide) (by decide)

/-- General execution of `dynamicCall` on a dirty physical window `[b, b + M)`: physical words in
the window may carry high-bit garbage `k * M`, while outside sentinels and `rGuard` survive. -/
private theorem exec_dynamicCall_dirty {W b x₁ x₂ : ℕ} (x : Data 16)
    (hb : x.regs rBase = b) (hxS : x.regs (scratch 0) = x₁ + x₂ + 4)
    (hm1 : x.mem (b + 1) % MemoryWindow.dynamicWindowSize 2 (x₁ + x₂ + 4) = x₁)
    (hm2 : x.mem (b + 2) % MemoryWindow.dynamicWindowSize 2 (x₁ + x₂ + 4) = x₂)
    (hfit : Fits W (b + 4 * MemoryWindow.dynamicWindowSize 2 (x₁ + x₂ + 4))) :
    let S := x₁ + x₂ + 4
    let M := MemoryWindow.dynamicWindowSize 2 S
    ∃ y : Data 16,
      ExecWithin W dynamicCall x y (13 * Nat.clog 2 S + 41) ∧
      y.regs (winBank (cOut.castAdd 3)) = x₁ + x₂ ∧
      y.mem (b + 3) % M = x₁ + x₂ ∧
      y.regs rGuard = x.regs rGuard ∧
      ∀ a, a < b ∨ b + M ≤ a → y.mem a = x.mem a := by
  obtain ⟨-, -, -, hSle, -, -⟩ :=
    MemoryWindow.dynamicWidth_fits (b := b) (widthCoeff := 2) (S := x₁ + x₂ + 4)
      (by decide) (by omega) hfit
  have h3 : Fits (MemoryWindow.dynamicWidth 2 (x₁ + x₂ + 4)) 3 := by
    change 3 < MemoryWindow.dynamicWindowSize 2 (x₁ + x₂ + 4)
    omega
  obtain ⟨z, y, hy, hymatch, ⟨hz_out, hz_mem3⟩, hyframe_mem, hyframe_regs⟩ :=
    MemoryWindow.exec_dynamicCallBank winBank_injective scratch_injective
      (by decide) (by decide) (by decide : 1 ≤ 2) (by omega)
      pairSumCallee_not_readsWidth x hb hxS hfit
      (T := 7)
      (Post := fun z => z.regs cOut = x₁ + x₂ ∧ z.mem 3 = x₁ + x₂)
      fun v _ hvmem => by
        have hv1 : v.mem 1 = x₁ := (hvmem 1).trans hm1
        have hv2 : v.mem 2 = x₂ := (hvmem 2).trans hm2
        have hsum : Fits (MemoryWindow.dynamicWidth 2 (x₁ + x₂ + 4)) (v.mem 1 + v.mem 2) := by
          rw [hv1, hv2]
          change x₁ + x₂ < MemoryWindow.dynamicWindowSize 2 (x₁ + x₂ + 4)
          omega
        obtain ⟨z, hz, hz1, hz2⟩ := exec_pairSumCallee v h3 hsum
        rw [hv1, hv2] at hz1 hz2
        exact ⟨z, hz, hz1, hz2⟩
  refine ⟨y, hy.mono (by omega), ?_, ?_, ?_, hyframe_mem⟩
  · exact (hymatch.regs cOut).trans hz_out
  · exact (hymatch.mem 3).trans hz_mem3
  · exact hyframe_regs rGuard (by decide) (by decide)

-- Concrete VM check on a dirty caller state (`b = 10, x₁ = 5, x₂ = 9, S = 18, M = 1024`):
-- physical cells `11` and `12` contain multiples of `1024` added to `5` and `9`, cell `13` holds
-- dirty `88888`, and sentinels at `9` (`< b`) and `1034` (`= b + M`) survive unchanged.
private def dirtyRun : Option (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  let b := 10
  let S := 18
  let M := MemoryWindow.dynamicWindowSize 2 S
  let x0 : Data 16 :=
    { regs := fun i => if i = rGuard then 777 else if i = rBase then b
        else if i = scratch 0 then S else 99999
      mem := fun a =>
        if a = 9 then 42
        else if a = b + 1 then 5 + 3 * M
        else if a = b + 2 then 9 + M
        else if a = b + 3 then 88888
        else if a = b + M then 91
        else 12345 }
  (dynamicCall.eval 20 64 x0).map fun (y, _) =>
    (y.regs rGuard, y.regs (winBank (cOut.castAdd 3)), y.mem (b + 3), y.mem 9, y.mem (b + M))

#guard dirtyRun == some (777, 14, 14, 42, 91)

/-! ### Initialized `FlatEndpoint` over `ℕ × ℕ` -/

private def entrySetup : Code .standard 16 :=
  let s0 := scratch 0
  let s1 := scratch 1
  ram[
    rGuard ← #77;
    rBase ← #4;
    rTmp ← #1; s0 ← *rTmp;
    rTmp ← #5; *rTmp ← s0;
    rTmp ← #2; s1 ← *rTmp;
    rTmp ← #6; *rTmp ← s1;
    s0 ← s0 + s1;
    rTmp ← #4; s0 ← s0 + rTmp ]

private def fullCode : Code .standard 16 :=
  let wOut := winBank (cOut.castAdd 3)
  .seq entrySetup (.seq dynamicCall (ram[ rOut ← wOut ]))

private abbrev sizeParam (p : ℕ × ℕ) : ℕ := p.1 + p.2 + 4

private abbrev winSize (p : ℕ × ℕ) : ℕ := MemoryWindow.dynamicWindowSize 2 (sizeParam p)

private def wMin (p : ℕ × ℕ) : ℕ := Nat.clog 2 (100 + 4 * winSize p) + 1

private def wordEnv (p : ℕ × ℕ) : ℕ := 4 * (100 + 4 * winSize p)

private def encodePair (p : ℕ × ℕ) : List ℕ := [p.1, p.2]

private def stepBudget (p : ℕ × ℕ) : ℕ := 13 * Nat.clog 2 (sizeParam p) + 55

private def postCond (p : ℕ × ℕ) (y : Data 16) : Prop :=
  y.regs rOut = p.1 + p.2 ∧ y.regs rGuard = 77 ∧ y.mem 0 = 2

private theorem pairSumEndpoint :
    FlatEndpoint fullCode rOut wMin wordEnv encodePair stepBudget postCond where
  not_readsWidth := by
    have he : ¬entrySetup.ReadsWidth := by decide
    have hd : ¬dynamicCall.ReadsWidth :=
      MemoryWindow.dynamicCallBank_not_readsWidth winBank scratch rBase 2
        pairSumCallee_not_readsWidth
    exact not_or.mpr ⟨he, not_or.mpr ⟨hd, by decide⟩⟩
  inputFits_min p := by
    have hfit : Fits (wMin p) (100 + 4 * winSize p) :=
      fits_of_clog_lt (by unfold wMin; omega)
    obtain ⟨-, -, -, hSle, -, -⟩ :=
      MemoryWindow.dynamicWidth_fits (b := 4) (widthCoeff := 2) (S := sizeParam p)
        (by decide) (by dsimp only [sizeParam]; omega) (hfit.of_le (by dsimp only [winSize]; omega))
    have hS : p.1 + p.2 + 4 ≤ winSize p := hSle
    refine ⟨hfit.of_le (by simp [encodePair]; omega), ?_⟩
    intro v hv
    simp only [encodePair, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hfit.of_le (by omega)
    · exact hfit.of_le (by omega)
  two_pow_wMin_le p := by
    let E := 100 + 4 * winSize p
    have hE : E ≠ 0 := by dsimp only [E]; omega
    have hp := Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ)) hE
    change 2 ^ (Nat.clog 2 E + 1) ≤ 4 * E
    rw [pow_succ]
    omega
  exec_min p := by
    have hfit0 : Fits (wMin p) (100 + 4 * winSize p) :=
      fits_of_clog_lt (by unfold wMin; omega)
    have hfit : Fits (wMin p) (4 + 4 * MemoryWindow.dynamicWindowSize 2 (p.1 + p.2 + 4)) :=
      hfit0.of_le (by dsimp only [winSize, sizeParam]; omega)
    obtain ⟨-, -, -, hSle, -, -⟩ :=
      MemoryWindow.dynamicWidth_fits (b := 4) (widthCoeff := 2) (S := p.1 + p.2 + 4)
        (by decide) (by omega) hfit
    have h77 : Fits (wMin p) 77 := hfit0.of_le (by omega)
    have h6 : Fits (wMin p) 6 := hfit0.of_le (by omega)
    have hsum1 : Fits (wMin p) (p.1 + p.2) := hfit.of_le (by omega)
    have hsum2 : Fits (wMin p) (p.1 + p.2 + 4) := hfit.of_le (by omega)
    generalize hstart : (Data.init (encodePair p) : Data 16) = x₀
    have hm0 : x₀.mem 0 = 2 := by rw [← hstart]; rfl
    have hm1 : x₀.mem 1 = p.1 := by rw [← hstart]; rfl
    have hm2 : x₀.mem 2 = p.2 := by rw [← hstart]; rfl
    obtain ⟨s, hs, sb, sS, sg, sm0, sm5, sm6⟩ :
        ∃ s : Data 16, ExecWithin (wMin p) entrySetup x₀ s 13 ∧
          s.regs rBase = 4 ∧ s.regs (scratch 0) = p.1 + p.2 + 4 ∧
          s.regs rGuard = 77 ∧ s.mem 0 = 2 ∧ s.mem 5 = p.1 ∧ s.mem 6 = p.2 := by
      refine ⟨?s, ?run, ?base, ?size, ?guard, ?m0, ?m5, ?m6⟩
      case run =>
        ram_eval [entrySetup, scratch, rGuard, rBase, rTmp, hm1, hm2,
          h77, h6, hsum1, hsum2, Fin.mk.injEq]
      case base => simp +decide [rBase]
      case size => simp +decide [scratch]
      case guard => simp +decide [rGuard]
      case m0 => exact hm0
      case m5 => simp +decide
      case m6 => simp +decide
    have hm5_mod : s.mem (4 + 1) % MemoryWindow.dynamicWindowSize 2 (p.1 + p.2 + 4) = p.1 := by
      rw [sm5]; exact Nat.mod_eq_of_lt (by omega)
    have hm6_mod : s.mem (4 + 2) % MemoryWindow.dynamicWindowSize 2 (p.1 + p.2 + 4) = p.2 := by
      rw [sm6]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨c, hc, hc_out, -, hc_guard, hc_frame⟩ :=
      exec_dynamicCall_dirty s sb sS hm5_mod hm6_mod hfit
    let y := c.set rOut (p.1 + p.2)
    have hret : ExecWithin (B := .standard) (wMin p)
        (.op (.copy rOut (winBank (cOut.castAdd 3)))) c y 1 := by
      simpa only [y, hc_out] using
        ExecWithin.copy (B := .standard) (w := wMin p) (x := c)
          (d := rOut) (s := winBank (cOut.castAdd 3))
    refine ⟨y, (hs.seq (hc.seq hret)).mono (by unfold stepBudget; dsimp only [sizeParam]; omega),
      ?_, ?_, ?_⟩
    · simp [y, rOut]
    · simpa +decide [y, rOut, rGuard, Function.update_apply] using hc_guard.trans sg
    · exact (hc_frame 0 (Or.inl (by decide))).trans sm0

-- Checked instance at arbitrary wider physical width (e.g. `W = 1024`) via `FlatEndpoint`:
example : ¬(fullCode.program rOut).ReadsWidth :=
  pairSumEndpoint.program_not_readsWidth

example : ∃ y n,
    n ≤ stepBudget (19, 23) ∧
    Runs 1024 (fullCode.program rOut) (State.init [19, 23]) ⟨fullCode.size, y⟩ n ∧
    Executes 1024 (fullCode.program rOut) (State.init [19, 23]) 42 (n + 1) ∧
    y.Bounded 1024 ∧ y.regs rGuard = 77 ∧ y.mem 0 = 2 := by
  have hW : wMin (19, 23) ≤ 1024 := by decide +kernel
  obtain ⟨y, n, hn, hruns, hexec, hbound, hout, hguard, hm0⟩ := pairSumEndpoint.runs (19, 23) hW
  refine ⟨y, n, hn, hruns, ?_, hbound, hguard, hm0⟩
  simpa [hout, encodePair] using hexec

-- Checked prefix-envelope bound across all wider widths `W ≥ wMin p`:
example {W k : ℕ} {s : State 16} (hW : wMin (19, 23) ≤ W)
    (hr : Runs W (fullCode.program rOut) (State.init [19, 23]) s k) :
    (∀ i, s.data.regs i < wordEnv (19, 23)) ∧
      (∀ q, s.data.mem q < wordEnv (19, 23)) ∧
      ∀ q, wordEnv (19, 23) ≤ q → s.data.mem q = 0 :=
  pairSumEndpoint.prefix_bounds (19, 23) hW hr

-- Nonvacuity check: `FlatEndpoint` is refutable for a false output claim (`999 ≠ 19 + 23`).
example : ¬FlatEndpoint fullCode rOut wMin wordEnv encodePair stepBudget
    (fun _ y => y.regs rOut = 999) := by
  intro hbad
  obtain ⟨y, _, -, -, hexec1, -, hbad_out⟩ := hbad.runs (19, 23) le_rfl
  obtain ⟨y', _, -, -, hexec2, -, hout, -, -⟩ := pairSumEndpoint.runs (19, 23) le_rfl
  rw [hbad_out] at hexec1
  rw [hout] at hexec2
  obtain ⟨hval, -⟩ := hexec1.unique hexec2
  omega

end CslibFrontierTests.WordRAMDynamicWindow
