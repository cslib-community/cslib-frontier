/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.ApproximateMembership.WordRAM.QuotientFilter.Cluster
public import CslibFrontier.Computability.WordRAM.Realization.Witness
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Tactic.FinIndex
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.SuppCases

/-!
# Word-RAM Register Layout and Lowered Cluster Code for the Quotient Filter

This module defines the register layout (`rQF`, `qfReg`, `kwiseMap`), multiply-shift remainder
seed sampling and evaluation (`remInitCode`, `remEvalCode`), and the lowered Word-RAM cluster
subroutine (`clusterCode`) assembled from `realizes_clusterOp` for the two-stage quotient filter.

## Main definitions

* `rQF`, `qfReg`, `kwiseMap`: register count and register-bank embeddings separating
  `ReducedKWise` (`0..239`), `SubroutineCode` control (`240..247`), and realized cluster scratch
  registers (`248..`).
* `remInitCode`, `remInitData`, `remInitComp`: randomized Word-RAM snippet and `ProbComp` model
  sampling the multiply-shift remainder seed.
* `remEvalCode`: deterministic Word-RAM snippet evaluating `remHash` in `45` instructions.
* `clusterCode`, `clusterFactor`: deterministic Word-RAM snippet staging `mkClusterInput` into
  registers `10..24` and running `realizes_clusterOp.code`, with its instruction exchange factor.

## Main results

* `remInitCode_execRand`, `map_extractRemSeed_eval_remInitComp`: `ExecRand` coupling and uniform
  `RemSeed` law for `remInitCode`.
* `remEvalCode_exec`: `45`-instruction execution and register-frame specification for
  `remEvalCode`.
* `clusterCode_execWithin`: `19 + clusterFactor * (11 * ℓ + 14)`-instruction execution
  specification coupling `clusterCode` to `clusterOpProg` under `FilterInv`.
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.Probability
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing

/-- Register count for the Word-RAM quotient filter: `0..239` shared with `ReducedKWise`,
`240..247` dedicated to `SubroutineCode` control and operation tags, and
`248 .. 248 + realizes_clusterOp.scratchSize` dedicated to the realized `Memory.Prog` scratch
registers. -/
@[expose] noncomputable def rQF : ℕ :=
  248 + (realizes_clusterOp.scratchSize + 1)

theorem le_rQF : 248 ≤ rQF := by
  dsimp only [rQF]
  omega

/-- Canonical embedding `Fin 248 → Fin rQF` for fixed control and hash registers. -/
@[expose] noncomputable def qfReg : Fin 248 → Fin rQF :=
  Fin.castLE le_rQF

theorem injective_qfReg : Function.Injective qfReg :=
  Fin.castLE_injective le_rQF

@[simp]
theorem qfReg_inj {i j : Fin 248} : qfReg i = qfReg j ↔ i = j :=
  injective_qfReg.eq_iff

@[simp]
theorem val_qfReg (i : Fin 248) : (qfReg i).val = i.val := rfl

/-- Embedding `Fin 240 → Fin rQF` for `ReducedKWise` subroutines. -/
@[expose] noncomputable def kwiseMap : Fin 240 → Fin rQF :=
  Fin.castLE (by dsimp only [rQF]; omega)

theorem injective_kwiseMap : Function.Injective kwiseMap :=
  Fin.castLE_injective _

@[simp]
theorem kwiseMap_eq_qfReg (i : Fin 240) :
    kwiseMap i = qfReg (Fin.castLE (by decide) i) := rfl

theorem extend_kwiseMap_regs {y : Data 240} {x : Data rQF} {j : Fin rQF} (hj : 240 ≤ j.val) :
    (y.extend kwiseMap x).regs j = x.regs j := by
  change Function.extend kwiseMap y.regs x.regs j = x.regs j
  apply Function.extend_apply'
  rintro ⟨i, rfl⟩
  have := i.isLt
  dsimp only [kwiseMap, Fin.val_castLE] at hj
  omega

/-- Sample the remainder seed `γ : RemSeed w₀` uniformly and store it at `remSeedAddr base w w₀ n`
using `5` instructions (`1` `rand` call). -/
noncomputable def remInitCode (w w₀ n : ℕ) : Code .exact rQF :=
  .seq (.op (.const (qfReg 30) (remSeedOff w w₀ n)))
  (.seq (.op (.exactBin .add (qfReg 30) (qfReg 0) (qfReg 30)))
  (.seq (.op (.const (qfReg 31) (2 ^ (w₀ - 1) - 1)))
  (.seq (.rand (qfReg 32) (qfReg 31))
        (.op (.store (qfReg 30) (qfReg 32))))))

/-- Closed-form machine state after `remInitCode w w₀ n` samples `γ`. -/
@[expose] noncomputable def remInitData (base w w₀ n : ℕ) (x : Data rQF) (γ : ℕ) : Data rQF :=
  (((x.set (qfReg 30) (remSeedOff w w₀ n)).set (qfReg 30) (remSeedAddr base w w₀ n)).set
    (qfReg 31) (2 ^ (w₀ - 1) - 1)).set (qfReg 32) γ |>.write (remSeedAddr base w w₀ n) γ

/-- Exact `ProbComp` semantics of `remInitCode w w₀ n`. -/
@[expose] noncomputable def remInitComp (base w w₀ n : ℕ) (x : Data rQF) :
    ProbComp (Data rQF × ℕ) := do
  let γ ← ProbComp.unifFin (2 ^ (w₀ - 1) - 1)
  pure (remInitData base w w₀ n x γ.val, 5)

theorem remInitCode_execRand {base w w₀ n k : ℕ} (hw₀ : w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {x : Data rQF} (h0 : x.regs (qfReg 0) = base) :
    ExecRand w (remInitCode w w₀ n) x (remInitComp base w w₀ n x) := by
  have hfit_addr : Fits w (base + remSeedOff w w₀ n) := by
    have : remSeedOff w w₀ n ≤ space w w₀ n k := by dsimp only [remSeedOff, space]; omega
    fits [this]
  have hfit_addr' : Fits w (remSeedAddr base w w₀ n) := hfit_addr
  have hfit_bound : Fits w (2 ^ (w₀ - 1) - 1) := by
    fits [Nat.pow_le_pow_right two_pos (by omega : w₀ - 1 ≤ w)]
  set s1 := x.set (qfReg 30) (remSeedOff w w₀ n)
  set s2 := s1.set (qfReg 30) (remSeedAddr base w w₀ n)
  set s3 := s2.set (qfReg 31) (2 ^ (w₀ - 1) - 1)
  have e2 : Exec w (.op (.exactBin .add (qfReg 30) (qfReg 0) (qfReg 30)) : Code .exact rQF)
      s1 s2 1 := by wram_exec [s1, h0, base_add_remSeedOff]
  have e4 := ExecRand.rand (B := .exact) (w := w) (dst := qfReg 32) (src := qfReg 31)
    (x := s3) (by simp [s3, hfit_bound])
  rw [show s3.regs (qfReg 31) = 2 ^ (w₀ - 1) - 1 by simp [s3]] at e4
  have e45 := ExecRand.seq
    (m₂ := fun d : Data rQF => pure (d.write (remSeedAddr base w w₀ n) (d.regs (qfReg 32)), 1))
    e4 fun z hz => by
      supp_cases hz with ⟨γ, rfl⟩
      have h1 := Exec.store (B := .exact) (w := w) (a := qfReg 30) (s := qfReg 32)
        (x := s3.set (qfReg 32) γ.val)
      rw [show (s3.set (qfReg 32) γ.val).regs (qfReg 30) = remSeedAddr base w w₀ n by
        simp +decide [s3, s2]] at h1
      exact h1.execRand
  have hall := (Exec.const (by fits)).seqRand (e2.seqRand ((Exec.const hfit_bound).seqRand e45))
  simpa only [remInitCode, remInitComp, remInitData, s3, s2, s1, bind_assoc, pure_bind,
    map_eq_bind_pure_comp, Function.comp_def, Data.set_regs, Function.update_self] using hall

theorem map_extractRemSeed_eval_remInitComp (base w w₀ n : ℕ) (x : Data rQF) :
    ((ProbComp.eval (remInitComp base w w₀ n x)).map fun z =>
      extractRemSeed base w w₀ n z.1.mem) =
      PMF.uniformOfFintype (RemSeed w₀) := by
  let e : Fin (2 ^ (w₀ - 1) - 1 + 1) ≃ RemSeed w₀ :=
    finCongr (Nat.sub_add_cancel Nat.one_le_two_pow)
  have hcomp :
      ((ProbComp.eval (remInitComp base w w₀ n x)).map fun z =>
        extractRemSeed base w w₀ n z.1.mem) =
        (ProbComp.eval (ProbComp.unifFin (2 ^ (w₀ - 1) - 1))).map e := by
    dsimp only [remInitComp]
    rw [ProbComp.eval_bind, PMF.map_bind]
    congr 1 with γ : 1
    simp only [ProbComp.eval_pure, PMF.pure_map, Function.comp_apply]
    congr 1
    apply Fin.ext
    have hlt : γ.val < 2 ^ (w₀ - 1) := by
      have := Nat.one_le_two_pow (n := w₀ - 1)
      have := γ.isLt
      omega
    dsimp only [extractRemSeed, remInitData, Data.write, Cslib.WordRAM.wordOfNat, e]
    simp [hlt]
  rw [hcomp, ProbComp.eval_unifFin, PMF.uniformOfFintype_map_equiv]

/-- Word-RAM snippet computing `(remHash U w₀ k γ u).val` into register `qfReg 3` from
`qfReg 0 = base` and `qfReg 1 = u.val`, using `ReducedKWise.reduceKeyCode w₀ w₀` in `45`
deterministic instructions. -/
noncomputable def remEvalCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (.op (.const (qfReg 30) (remSeedOff w w₀ n)))
  (.seq (.op (.exactBin .add (qfReg 0) (qfReg 0) (qfReg 30)))
  (.seq ((ReducedKWise.reduceKeyCode w₀ w₀).rename kwiseMap)
  (.seq (.op (.const (qfReg 30) (remSeedOff w w₀ n)))
  (.seq (.op (.exactBin .sub (qfReg 0) (qfReg 0) (qfReg 30)))
  (.seq (.op (.const (qfReg 30) (w₀ - remBits w₀ k)))
        (.op (.exactBin .shiftRight (qfReg 3) (qfReg 3) (qfReg 30))))))))

theorem remEvalCode_exec {base w U w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k))
    (γ : RemSeed w₀) (u : Fin U) {x : Data rQF}
    (h0 : x.regs (qfReg 0) = base) (h1 : x.regs (qfReg 1) = u.val)
    (hseed : x.mem (remSeedAddr base w w₀ n) = γ.val) :
    ∃ y : Data rQF,
      Exec w (remEvalCode w w₀ n k) x y 45 ∧
      y.mem = x.mem ∧
      y.regs (qfReg 0) = base ∧
      y.regs (qfReg 3) = (remHash U w₀ k γ u).val ∧
      ∀ j : Fin rQF, 240 ≤ j.val → y.regs j = x.regs j := by
  have hfit_addr : Fits w (base + remSeedOff w w₀ n) := by
    have : remSeedOff w w₀ n ≤ space w w₀ n k := by dsimp only [remSeedOff, space]; omega
    fits [this]
  have hfit_addr' : Fits w (remSeedAddr base w w₀ n) := hfit_addr
  have hfit_sh : Fits w (w₀ - remBits w₀ k) := by
    fits [hw₀, @Nat.lt_two_pow_self w]
  have hrem_eq : oddMulModWord w₀ γ.val u.val >>> (w₀ - remBits w₀ k) =
      (remHash U w₀ k γ u).val := by
    have hsh : w₀ - remBits w₀ k = w₀ - (k + 1) := by dsimp only [remBits]; omega
    rw [hsh]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced (R := k + 1) hw₀_pos γ u
  have hfit_rem : Fits w (remHash U w₀ k γ u).val := by
    fits [(remHash U w₀ k γ u).isLt, Nat.pow_le_pow_right two_pos ((remBits_le_w₀ w₀ k).trans hw₀)]
  have hmin : min w₀ (3 * w₀) = w₀ := min_eq_left (by omega)
  have hle : remSeedOff w w₀ n ≤ remSeedAddr base w w₀ n := by simp [remSeedAddr, remSeedOff]
  have hsub : remSeedAddr base w w₀ n - remSeedOff w w₀ n = base := by
    simp [remSeedAddr, remSeedOff]
  have hk1 : kwiseMap 1 = qfReg 1 := rfl
  unfold remEvalCode
  wram_exec [h0, show base + remSeedOff w w₀ n = remSeedAddr base w w₀ n from rfl]
  wram_call (ReducedKWise.reduceKeyCode_exec (b := w₀) hw₀_pos hw₀
    (((x.set (qfReg 30) (remSeedOff w w₀ n)).set (qfReg 0) (remSeedAddr base w w₀ n)).comap
      kwiseMap)
    (by simp only [Data.comap_mem, Data.comap_regs]; wram_simp [hseed]; exact γ.isLt)
    (by simp only [Data.comap_regs]; wram_simp [hk1, h1]; exact u.isLt.trans_le hU))
    renamed injective_kwiseMap with y₀ ⟨⟨hy₀_0, hy₀_3, hy₀_mem⟩, hframe⟩
  have hy0 : y₀.regs (qfReg 0) = remSeedAddr base w w₀ n := by
    rw [show qfReg 0 = kwiseMap 0 from rfl, hy₀_0]
    wram_simp
  have hy3 : y₀.regs (qfReg 3) = oddMulModWord w₀ γ.val u.val := by
    rw [show qfReg 3 = kwiseMap 3 from rfl, hy₀_3]
    wram_simp [hseed, hk1, h1, hmin, Nat.shiftRight_zero]
  wram_exec [hy0, hy3, hsub, hrem_eq]
  refine ⟨by wram_simp [hy₀_mem], by wram_simp, by wram_simp, fun j hj => ?_⟩
  have hj0 : j ≠ qfReg 0 := by fin_index [val_qfReg]
  have hj3 : j ≠ qfReg 3 := by fin_index [val_qfReg]
  have hj30 : j ≠ qfReg 30 := by fin_index [val_qfReg]
  wram_simp
  rw [hframe j fun i h => by subst h; simp at hj; omega]
  wram_simp

/-- Load `base + off` into `qfReg d` (for `d ≠ 0`) from `qfReg 0 = base` in `2` instructions. -/
private noncomputable def loadOffCode (d : Fin 248) (off : ℕ) : Code .exact rQF :=
  .seq (.op (.const (qfReg d) off))
       (.op (.exactBin .add (qfReg d) (qfReg 0) (qfReg d)))

private theorem loadOffCode_exec {base w off : ℕ} {d : Fin 248} (hd : d ≠ 0)
    (hfit : Fits w (base + off)) {x : Data rQF} (h0 : x.regs (qfReg 0) = base) :
    Exec w (loadOffCode d off) x (x.set (qfReg d) (base + off)) 2 := by
  have hd' : qfReg 0 ≠ qfReg d := by simp [qfReg_inj, hd.symm]
  unfold loadOffCode
  wram_exec [h0]
  cases x
  simp [Data.set]

/-- Source register map `Fin 15 → Fin rQF` (`qfReg 10 .. qfReg 24`) for `clusterOpProg`. -/
private noncomputable def clusterSrcRegs (i : Fin (WordEncoding.width ClusterInput)) : Fin rQF :=
  qfReg ⟨10 + i.val, by have hi : i.val < 15 := i.isLt; omega⟩

/-- Load the 15 words of `mkClusterInput base w w₀ n k q r opTag` into `qfReg 10 .. qfReg 24`
from `qfReg 0 = base`, `qfReg 2 = q.val`, `qfReg 3 = r.val`, `qfReg 247 = opTag` in `19`
instructions. -/
private noncomputable def loadClusterInputCode (w w₀ n k : ℕ) : Code .exact rQF :=
  let b := quotBits w₀ n
  let f := remBits w₀ k
  let pBit := slotPackShift b 1 w
  let pRem := slotPackShift b f w
  .seq (.op (.copy (qfReg 10) (qfReg 2)))
  (.seq (.op (.copy (qfReg 11) (qfReg 3)))
  (.seq (.op (.copy (qfReg 12) (qfReg 247)))
  (.seq (.op (.const (qfReg 13) (2 ^ b)))
  (.seq (.op (.const (qfReg 14) (2 ^ b - 1)))
  (.seq (loadOffCode 15 (fullOff w w₀ n))
  (.seq (loadOffCode 16 (occOff w w₀ n))
  (.seq (loadOffCode 17 (runOff w w₀ n))
  (.seq (loadOffCode 18 (remOff w w₀ n))
  (.seq (.op (.const (qfReg 19) pBit))
  (.seq (.op (.const (qfReg 20) (2 ^ pBit - 1)))
  (.seq (.op (.const (qfReg 21) pRem))
  (.seq (.op (.const (qfReg 22) (2 ^ pRem - 1)))
  (.seq (.op (.const (qfReg 23) f))
        (.op (.const (qfReg 24) (2 ^ f - 1))))))))))))))))

/-- Closed-form machine state after `loadClusterInputCode w w₀ n k`. -/
private noncomputable def loadClusterInputData (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (x : Data rQF) : Data rQF :=
  let d := mkClusterInput base w w₀ n k q r opTag
  (((((((((((((((x.set (qfReg 10) d.qVal).set (qfReg 11) d.rVal).set (qfReg 12) d.opTag).set
    (qfReg 13) d.slotCap).set (qfReg 14) d.slotMask).set (qfReg 15) d.fullBase).set
    (qfReg 16) d.occBase).set (qfReg 17) d.runBase).set (qfReg 18) d.remBase).set
    (qfReg 19) d.pBit).set (qfReg 20) d.pBitMask).set (qfReg 21) d.pRem).set
    (qfReg 22) d.pRemMask).set (qfReg 23) d.f).set (qfReg 24) d.fMask)

private theorem loadClusterInputCode_exec {base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k))
    {opTag : ℕ} (hop : opTag < 4)
    {x : Data rQF}
    (h0 : x.regs (qfReg 0) = base)
    (h2 : x.regs (qfReg 2) = q.val)
    (h3 : x.regs (qfReg 3) = r.val)
    (h247 : x.regs (qfReg 247) = opTag)
    (hfr : x.regs (qfReg 240) = base + space w w₀ n k) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let x₁ := loadClusterInputData base w w₀ n k q r opTag x
    Exec w (loadClusterInputCode w w₀ n k) x x₁ 19 ∧
    x₁.mem = x.mem ∧
    x₁.regs (qfReg 0) = base ∧
    x₁.regs (qfReg 240) = base + space w w₀ n k ∧
    x₁.regs ∘ clusterSrcRegs = WordEncoding.encode d := by
  intro d x₁
  have hsafe := clusterSafe_mkClusterInput hw₀_pos hw hfit_space q r hop
  have hfit_i (i : Fin (WordEncoding.width ClusterInput)) : Fits w (WordEncoding.encode d i) :=
    hsafe.fits_encode i
  have hf3 : Fits w (2 ^ quotBits w₀ n) := hfit_i 3
  have hf4 : Fits w (2 ^ quotBits w₀ n - 1) := hfit_i 4
  have hf9 : Fits w (slotPackShift (quotBits w₀ n) 1 w) := hfit_i 9
  have hf10 : Fits w (2 ^ slotPackShift (quotBits w₀ n) 1 w - 1) := hfit_i 10
  have hf11 : Fits w (slotPackShift (quotBits w₀ n) (remBits w₀ k) w) := hfit_i 11
  have hf12 : Fits w (2 ^ slotPackShift (quotBits w₀ n) (remBits w₀ k) w - 1) := hfit_i 12
  have hf13 : Fits w (remBits w₀ k) := hfit_i 13
  have hf14 : Fits w (2 ^ remBits w₀ k - 1) := hfit_i 14
  refine ⟨?_, rfl, by simp +decide [x₁, loadClusterInputData, h0],
    by simp +decide [x₁, loadClusterInputData, hfr], ?_⟩
  · unfold loadClusterInputCode
    wram_exec [h2, h3, h247]
    refine WP.Exact.of_exec (loadOffCode_exec (d := 15) (by decide)
      (by rw [base_add_fullOff]; exact hfit_i 5) (by wram_simp [h0])) ?_
    wram_exec
    refine WP.Exact.of_exec (loadOffCode_exec (d := 16) (by decide)
      (by rw [base_add_occOff]; exact hfit_i 6) (by wram_simp [h0])) ?_
    wram_exec
    refine WP.Exact.of_exec (loadOffCode_exec (d := 17) (by decide)
      (by rw [base_add_runOff]; exact hfit_i 7) (by wram_simp [h0])) ?_
    wram_exec
    refine WP.Exact.of_exec (loadOffCode_exec (d := 18) (by decide)
      (by rw [base_add_remOff]; exact hfit_i 8) (by wram_simp [h0])) ?_
    wram_exec
    simp only [x₁, loadClusterInputData, mkClusterInput, base_add_fullOff, base_add_occOff,
      base_add_runOff, base_add_remOff]
  funext i
  change x₁.regs (clusterSrcRegs i) = ClusterInput.words d i
  fin_cases i <;> (simp +decide [x₁, loadClusterInputData, clusterSrcRegs]; rfl)

/-- Output and scratch register map `Fin (1 + scratchSize + 1) → Fin rQF` for `clusterOpProg`:
coordinate `0` is `qfReg 1` (the operation output register), and coordinates `j > 0` are
`248 + (j - 1)`. -/
private noncomputable def clusterTmpRegs
    (j : Fin (WordEncoding.width ℕ + realizes_clusterOp.scratchSize + 1)) : Fin rQF :=
  if j.val = 0 then qfReg 1
  else ⟨248 + (j.val - 1), by
    have hj : j.val < 1 + realizes_clusterOp.scratchSize + 1 := j.isLt
    dsimp only [rQF]
    omega⟩

@[simp]
private theorem val_clusterTmpRegs
    (j : Fin (WordEncoding.width ℕ + realizes_clusterOp.scratchSize + 1)) :
    (clusterTmpRegs j).val = if j.val = 0 then 1 else 248 + (j.val - 1) := by
  dsimp only [clusterTmpRegs]
  split_ifs <;> rfl

private theorem injective_clusterTmpRegs : Function.Injective clusterTmpRegs := by
  fin_index [val_clusterTmpRegs]

private theorem clusterSrcRegs_ne_clusterTmpRegs (i : Fin (WordEncoding.width ClusterInput))
    (j : Fin (WordEncoding.width ℕ + realizes_clusterOp.scratchSize + 1)) :
    clusterSrcRegs i ≠ clusterTmpRegs j := by
  have hi : i.val < 15 := i.isLt
  fin_index [clusterSrcRegs, val_clusterTmpRegs, val_qfReg]

private theorem clusterTmpRegs_ne_qfReg {k : Fin 248} (hk : k.val ≠ 1)
    (j : Fin (WordEncoding.width ℕ + realizes_clusterOp.scratchSize + 1)) :
    clusterTmpRegs j ≠ qfReg k := by
  fin_index [val_clusterTmpRegs, val_qfReg]

private theorem clusterSrcRegs_ne_frontier (i : Fin (WordEncoding.width ClusterInput)) :
    clusterSrcRegs i ≠ qfReg 240 := by
  have hi : i.val < 15 := i.isLt
  fin_index [clusterSrcRegs, val_qfReg]

/-- Combined Word-RAM code loading `mkClusterInput` into registers `qfReg 10 .. qfReg 24` and
running the realized `clusterOpProg` code with frontier `qfReg 240` and output in `qfReg 1`. -/
noncomputable def clusterCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (loadClusterInputCode w w₀ n k)
    (realizes_clusterOp.code (qfReg 240) clusterSrcRegs clusterTmpRegs)

/-- Exchange factor of the realized cluster `Memory.Prog` program. -/
noncomputable def clusterFactor : ℕ :=
  realizes_clusterOp.factor

theorem clusterCode_execWithin {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    (u : Fin U) {opTag : ℕ} (hop : opTag < 4)
    {x : Data rQF}
    (hx : x.Bounded w)
    (h0 : x.regs (qfReg 0) = base)
    (hfr : x.regs (qfReg 240) = base + space w w₀ n k)
    (h2 : x.regs (qfReg 2) = (quot u).val)
    (h3 : x.regs (qfReg 3) = (rem u).val)
    (h247 : x.regs (qfReg 247) = opTag)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k x.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    let d := mkClusterInput base w w₀ n k (quot u) (rem u) opTag
    let s₀ : Memory.State := ⟨x.mem, base + space w w₀ n k⟩
    ∃ y : Data rQF,
      ExecWithin w (clusterCode w w₀ n k) x y
        (19 + clusterFactor * (11 * hinv.clusterLen hS_lt (quot u) + 14)) ∧
      y.Bounded w ∧
      y.regs (qfReg 0) = base ∧
      y.regs (qfReg 240) = ((Memory.spec 0).clientState s₀ (clusterOpProg d)).frontier ∧
      y.regs (qfReg 1) = (Memory.spec 0).clientResult s₀ (clusterOpProg d) ∧
      y.mem = ((Memory.spec 0).clientState s₀ (clusterOpProg d)).mem := by
  intro d s₀
  obtain ⟨he₁, hx₁_mem, hx₁_0, hx₁_fr, hx₁_src⟩ :=
    loadClusterInputCode_exec hw₀_pos hw hfit_space (quot u) (rem u) hop h0 h2 h3 h247 hfr
  set x₁ := loadClusterInputData base w w₀ n k (quot u) (rem u) opTag x
  have hms_eq : memoryState (qfReg 240) x₁ = s₀ := by
    dsimp only [memoryState, s₀]; rw [hx₁_mem, hx₁_fr]
  have hsafe := clusterSafe_mkClusterInput hw₀_pos hw hfit_space (quot u) (rem u) hop
  obtain ⟨y, hy_exec, hy_ms, hy_out, hy_frame⟩ :=
    (realizes_clusterOp.code_spec (qfReg 240) clusterSrcRegs clusterTmpRegs
      injective_clusterTmpRegs clusterSrcRegs_ne_clusterTmpRegs
      (clusterTmpRegs_ne_qfReg (k := 240) (by decide)) clusterSrcRegs_ne_frontier).2
      w d x₁ (he₁.within.bounded hx) hx₁_src hsafe
      (validHistory_clusterOp_mk (wellFormed_memoryState (he₁.within.bounded hx))
        (by rw [hms_eq]) (quot u) (rem u) hsafe)
  rw [hms_eq, clientState_width w (clusterOpProg d) s₀] at hy_ms
  have hcost_le :
      realizes_clusterOp.factor *
        (memoryCost (clusterOpProg d) (memoryState (qfReg 240) x₁) + 0 + 1) ≤
      clusterFactor * (11 * hinv.clusterLen hS_lt (quot u) + 14) := by
    rw [hms_eq]
    apply Nat.mul_le_mul_left
    have hmc := memoryCost_clusterOp_mk_le base w w₀ n k (quot u) (rem u) opTag s₀ hinv hS_lt
    dsimp only [d]
    omega
  exact ⟨y, he₁.within.seq (hy_exec.mono hcost_le), hy_exec.bounded (he₁.within.bounded hx),
    by rw [hy_frame (qfReg 0) (by decide) (clusterTmpRegs_ne_qfReg (k := 0) (by decide)), hx₁_0],
    congrArg Memory.State.frontier hy_ms,
    by have h := hy_out 0; rw [hms_eq, clientResult_width w (clusterOpProg d) s₀] at h; exact h,
    congrArg Memory.State.mem hy_ms⟩

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
