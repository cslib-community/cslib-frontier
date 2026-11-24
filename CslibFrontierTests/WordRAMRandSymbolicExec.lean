/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of randomized symbolic execution)

public import CslibFrontier.Computability.WordRAM.Allocation
public import CslibFrontier.Computability.WordRAM.ExactNotation
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Randomized.SymbolicExec
public import CslibFrontier.Computability.WordRAM.Resizable.Randomized
import CslibFrontier.Tactic.SuppCases

/-!
# Tests for `WP.Rand`, `WP.RandWithin`, `WP.Dist`, `wram_rand_exec`, and `wram_rand_call`
-/

public section

open Cslib Cslib.WordRAM
open scoped ENNReal

/-- Test register 0. -/
abbrev regA : Fin 4 := 0
/-- Test register 1. -/
abbrev regB : Fin 4 := 1
/-- Test register 2. -/
abbrev regC : Fin 4 := 2
/-- Test register 3. -/
abbrev regD : Fin 4 := 3

/-! ## `ExecRand` straight-line deterministic + `rand` execution -/

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 1)) :
    ExecRand (B := .exact) w ram[ regB ← #1; regC ← rand regA ] x
      (do
        let k ← ProbComp.unifFin a
        pure ((x.set regB 1).set regC k.val, 2)) := by
  wram_rand_exec [ha]

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hb : x.regs regD = 1)
    (hfit : Fits w (a + 1)) :
    ExecRand w ram[ regB ← rand regA; regC ← regB + regD ] x
      (do
        let k ← ProbComp.unifFin a
        pure ((x.set regB k.val).set regC (k.val + 1), 2)) := by
  wram_rand_exec [ha, hb]

example {w a base : ℕ} {x : Data 4} (ha : x.regs regA = a) (hptr : x.regs regC = base)
    (hone : x.regs regD = 1) (hfit_ptr : Fits w (base + 1)) (hfit_a : Fits w a) :
    ExecRand w ram[ regB ← rand regA; *regC ← regB; regC ← regC + regD ] x
      (do
        let k ← ProbComp.unifFin a
        pure (((x.set regB k.val).write base k.val).set regC (base + 1), 3)) := by
  wram_rand_exec [ha, hptr, hone]

/-! ## An instruction given by a definition (`Op.addAdditive`, over `Basis.additive`) -/

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 1))
    (hsum : Fits w (a + a)) :
    ExecRand (B := .additive) w (.seq (.op (.addAdditive regB regA regA)) (.rand regC regA)) x
      (do
        let k ← ProbComp.unifFin a
        pure ((x.set regB (a + a)).set regC k.val, 2)) := by
  wram_rand_exec [ha]

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 1))
    (hsum : Fits w (a + a)) :
    ExecRand (B := .additive) w (.seq (.rand regC regA) (.op (.addAdditive regB regA regA))) x
      (do
        let k ← ProbComp.unifFin a
        pure ((x.set regC k.val).set regB (a + a), 2)) := by
  wram_rand_exec [ha]

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hsum : Fits w (a + a)) :
    ExecRand (B := .additive) w (.op (.addAdditive regB regA regA)) x
      (pure (x.set regB (a + a), 1)) := by
  wram_rand_exec [ha]

/-! ## Left-nested `.seq` reassociation (`seq_assoc`) -/

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 1)) :
    ExecRand (B := .exact) w
      (.seq (.seq (.op (.const regB 0)) (.op (.const regD 1))) (.rand regC regA)) x
      (do
        let k ← ProbComp.unifFin a
        pure (((x.set regB 0).set regD 1).set regC k.val, 3)) := by
  wram_rand_exec [ha]

/-! ## Conditional branches inside `ExecRand` and `ExecRandWithin` -/

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hb : x.regs regB = 0)
    (hfit : Fits w (a + 1)) (hpos : 0 < a) :
    ExecRand (B := .exact) w ram[
      if regB < regA then [ regC ← rand regA ] else [ regC ← #0 ]
    ] x (do let k ← ProbComp.unifFin a; pure (x.set regC k.val, 2)) := by
  wram_rand_exec [ha, hb]

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hb : x.regs regB = 1)
    (hfit : Fits w (a + 1)) :
    ExecRandWithin (B := .exact) w ram[
      if regA = regB then [ regC ← #0 ] else [ regC ← rand regA ]
    ] x (fun y => y.regs regC ≤ a) 3 1 := by
  wram_rand_exec [ha, hb]
  · simp
  · intro k; wram_simp; have := k.isLt; omega

/-! ## `wram_rand_call` with deterministic, randomized, and renamed contracts -/

private abbrev r2_0 : Fin 2 := 0
private abbrev r2_1 : Fin 2 := 1

private def subStep : Code .exact 2 := ram_exact[ r2_0 ← #1 ]

private theorem subStep_exec {w : ℕ} {x : Data 2} (h1 : Fits w 1) :
    Exec w subStep x (x.set 0 1) 1 := by
  unfold subStep; wram_exec

private def subRand : Code .exact 2 := .rand r2_0 r2_1

private theorem subRand_exec {w a : ℕ} {x : Data 2} (ha : x.regs r2_1 = a) (hfit : Fits w a) :
    ExecRand w subRand x (do let k ← ProbComp.unifFin a; pure (x.set r2_0 k.val, 1)) := by
  unfold subRand; wram_rand_exec [ha]

private def map2to4 : Fin 2 → Fin 4
  | 0 => regB
  | 1 => regA

private theorem injective_map2to4 : Function.Injective map2to4 := by decide

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 1)) :
    ExecRand (B := .exact) w (.seq (subStep.rename map2to4) (.rand regC regA)) x
      (do
        let k ← ProbComp.unifFin a
        pure ((x.set regB 1).set regC k.val, 2)) := by
  refine WP.Rand.execRand ?_
  wram_rand_call (subStep_exec (x := x.comap map2to4) (by fits)) renamed injective_map2to4
  wram_rand_exec [ha, Data.extend_set injective_map2to4,
    Data.extend_comap injective_map2to4, map2to4]
  simp only [← bind_pure_comp, bind_assoc, pure_bind, Data.extend_set injective_map2to4,
    Data.extend_comap injective_map2to4, map2to4]

/-- Metavar-inferred continuation across `wram_rand_call ... renamed ... with y n hz`. -/
example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 1)) :
    ExecRand (B := .exact) w (.seq (subRand.rename map2to4) (.op (.const regD 1))) x
      (do
        let z₁ ← (do let k ← ProbComp.unifFin a; pure ((x.comap map2to4).set r2_0 k.val, 1))
        pure ((z₁.1.extend map2to4 x).set regD 1, z₁.2 + 1)) := by
  refine WP.Rand.execRand ?_
  wram_rand_call (subRand_exec ha (by fits)) renamed injective_map2to4 with y n _
  · wram_rand_exec
  · simp only [bind_assoc, pure_bind]

/-! ## `ExecRandWithin` straight-line and `ExecCodeDist` chaining -/

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 2)) :
    ExecRandWithin (B := .exact) w ram[ regB ← #1; regC ← rand regA ] x
      (fun y => y.regs regB = 1 ∧ y.regs regC ≤ a) 2 1 := by
  wram_rand_exec [ha]
  intro k
  refine ⟨by wram_simp, ?_⟩
  wram_simp; have := k.isLt; omega

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 2)) :
    ExecCodeDist (B := .exact) w ram[ regB ← #1; regC ← rand regA ] x
      ((ProbComp.unifFin a).eval.map fun k => (x.set regB 1).set regC k.val) 2 := by
  wram_rand_exec [ha]

/-! ## `wram_rand_exec -split` and shared `ExecRand` / `ExecCodeDist` combinators -/

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 2)) :
    ExecRand (B := .exact) w ram_exact[
      regB ← #0;
      if regB < regA then [ regC ← #1 ] else [ regC ← #2 ]
    ] x (pure (((x.set regB 0).set regC (if 0 < a then 1 else 2)), if 0 < a then 3 else 4)) := by
  wram_rand_exec -split [ha]
  by_cases h : 0 < a <;> wram_rand_exec [h, ha] <;> simp [h]

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 1)) :
    ExecRand (B := .exact) w (.seq (.rand regC regA) ram_exact[ regB ← #1 ]) x
      ((fun z => (z.1.set regB 1, z.2 + 1)) <$>
        (do let k ← ProbComp.unifFin a; pure (x.set regC k.val, 1))) := by
  have h1 : ExecRand (B := .exact) w (.rand regC regA) x
      (do let k ← ProbComp.unifFin a; pure (x.set regC k.val, 1)) := by
    wram_rand_exec [ha]
  exact ExecRand.seq_det h1 fun y _ _ =>
    Exec.const (B := .exact) (w := w) (x := y) (d := regB) (v := 1) (by fits)

example {w a : ℕ} {x : Data 4} (ha : x.regs regA = a) (hfit : Fits w (a + 1)) :
    ExecCodeDist (B := .exact) w (.rand regC regA) x
      ((ProbComp.unifFin a).eval.map fun k => x.set regC k.val) 1 := by
  have h1 : ExecRand (B := .exact) w (.rand regC regA) x
      (do let k ← ProbComp.unifFin a; pure (x.set regC k.val, 1)) := by
    wram_rand_exec [ha]
  refine (ExecCodeDist.of_execRand_le (T := 1) h1 fun z hz => ?_).congr_dist ?_ Nat.cast_one.le
  · supp_cases hz; exact le_rfl
  · rw [ProbComp.eval_bind, PMF.map_bind]
    refine congrArg ((ProbComp.unifFin a).eval.bind ·) (funext fun k => ?_)
    ext z; simp [ProbComp.eval_pure, PMF.map]

/-! ## `Resizable.ExecRandBounded` → `ExecRCodeDist` bridge -/

example {w L_peak a : ℕ} {x : Resizable.RData 4}
    (hL : x.frontier ≤ L_peak) (ha : x.regs regA = a) (hfit : Fits w a) :
    Resizable.ExecRCodeDist (B := .exact) w
      (Resizable.RCode.ofCode (.rand regC regA)) x
      ((ProbComp.unifFin a).eval.map fun k => x.set regC k.val) 1 L_peak := by
  have hfit' : Fits w (x.toData.regs regA) := by simpa [Resizable.RData.toData, ha] using hfit
  have hb : Resizable.ExecRandBounded (B := .exact) w 0 (.rand regC regA) x.toData
      (do let k ← ProbComp.unifFin a; pure (x.toData.set regC k.val, 1)) := by
    have h0 := Resizable.ExecRandBounded.rand (B := .exact) (w := w) (L := 0)
      (dst := regC) (src := regA) (x := x.toData) hfit'
    rwa [show x.toData.regs regA = a from ha] at h0
  refine (Resizable.ExecRCodeDist.of_execRandBounded hL (Nat.zero_le _) hb).congr_dist ?_ ?_
  · rw [ProbComp.eval_bind, PMF.map_bind]
    refine congrArg ((ProbComp.unifFin a).eval.bind ·) (funext fun k => ?_)
    ext z; simp [ProbComp.eval_pure, PMF.map, Resizable.RData.set, Data.set]
  · rw [ProbComp.expect_bind]
    simp only [ProbComp.expect_pure, Nat.cast_one, ProbComp.expect_const, le_rfl]

end
