/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.WitnessScan.Cell
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.WitnessScan.Setup
public import CslibFrontier.Computability.GenericRAM.Signed.Fits
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Tactic.StrideOmega

/-!
# Complete native original-weight interval verification

Every interval vertex is tested by actual charged code. The returned flag characterizes
existence of an original zero sum, and a successful run returns an original-coordinate witness.
Arguments and all memory are preserved. The magnitude and address bounds here are numerical
component premises; the producer/product consumer derives them from its original input.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan

open Cslib.WordRAM

private theorem args_of_eq (A : Args) {x y : Data 32} (hx : A.InRegisters x)
    (h : ∀ i : Fin 32, 9 ≤ i.val → i.val < 17 → y.regs i = x.regs i) :
    A.InRegisters y := by
  simpa only [Args.InRegisters, h Reg.ab (by decide) (by decide),
    h Reg.bc (by decide) (by decide), h Reg.ac (by decide) (by decide),
    h Reg.size (by decide) (by decide), h Reg.a (by decide) (by decide),
    h Reg.b (by decide) (by decide), h Reg.first (by decide) (by decide),
    h Reg.length (by decide) (by decide)] using hx

/-- Read and verify the original signed arrays, preserving the argument bank and all memory.
The bound excludes only a final halt. The success flag is raw unsigned 0/1; the witness is an
original vertex, not a middle-label or modular candidate. -/
theorem exec {w U : ℕ} (A : Args) (AB BC AC : ℕ → ℕ → ℤ) (x : Data 32)
    (hx : A.InRegisters x) (ha : A.a < A.n) (hb : A.b < A.n)
    (hc : A.first + A.length ≤ A.n)
    (hmem : ∀ i < A.n, ∀ j < A.n,
      x.mem (A.ab + (i * A.n + j)) = Signed.encode (AB i j) ∧
      x.mem (A.bc + (i * A.n + j)) = Signed.encode (BC i j) ∧
      x.mem (A.ac + (i * A.n + j)) = Signed.encode (AC i j))
    (hmag : ∀ i < A.n, ∀ j < A.n,
      (AB i j).natAbs ≤ U ∧ (BC i j).natAbs ≤ U ∧ (AC i j).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2) A.addressBound) :
    ∃ y, ExecWithin (w + 2) program x y (42 * A.length + 17) ∧
      A.InRegisters y ∧ y.mem = x.mem ∧ (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      (y.regs Reg.found = 1 ↔ ∃ c, A.first ≤ c ∧ c < A.first + A.length ∧
        AB A.a A.b + BC A.b c + AC A.a c = 0) ∧
      (y.regs Reg.found = 1 → A.first ≤ y.regs Reg.witness ∧
        y.regs Reg.witness < A.first + A.length ∧
        AB A.a A.b + BC A.b (y.regs Reg.witness) + AC A.a (y.regs Reg.witness) = 0) := by
  let total (c : ℕ) := AB A.a A.b + BC A.b c + AC A.a c
  obtain ⟨s, hs, sargs, smem, sone, szero, sfound, sindex, srowB, srowA, swab⟩ :=
    exec_setup A x (AB A.a A.b) hx ha hb hc (hmem A.a ha A.b hb).1 hfit
  let I (y : Data 32) : Prop := A.InRegisters y ∧ y.mem = x.mem ∧
    y.regs Reg.one = 1 ∧ y.regs Reg.zero = 0 ∧
    y.regs Reg.rowB = A.bc + A.b * A.n + A.first ∧
    y.regs Reg.rowA = A.ac + A.a * A.n + A.first ∧
    y.regs Reg.wab = Signed.encode (AB A.a A.b) ∧ y.regs Reg.index ≤ A.length ∧
    (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
    (y.regs Reg.found = 1 ↔ ∃ j < y.regs Reg.index, total (A.first + j) = 0) ∧
    (y.regs Reg.found = 1 → A.first ≤ y.regs Reg.witness ∧
      y.regs Reg.witness < A.first + y.regs Reg.index ∧ total (y.regs Reg.witness) = 0)
  have hstart : I s := ⟨sargs, smem, sone, szero, srowB, srowA, swab, by omega, Or.inl sfound,
    ⟨fun _ => by omega, fun ⟨_, _, _⟩ => by omega⟩, fun _ => by omega⟩
  have hrowB : A.b * A.n + A.first ≤ A.n * A.n := by stride_omega
  have hrowA : A.a * A.n + A.first ≤ A.n * A.n := by stride_omega
  have hbody (y : Data 32) (hy : I y) (hc' : (Cond.lt Reg.index Reg.length).Holds y) :
      ∃ z, ExecWithin (w + 2) step y z 40 ∧ I z ∧
        A.length - z.regs Reg.index < A.length - y.regs Reg.index := by
    obtain ⟨yargs, ymem, yone, yzero, yrowB, yrowA, ywab, yindex, yflag, yiff, ywit⟩ := hy
    have yl : y.regs Reg.length = A.length := yargs.2.2.2.2.2.2.2
    have hi : y.regs Reg.index < A.length := yl ▸ Cond.holds_lt.mp hc'
    let i := y.regs Reg.index
    have hcurrent : A.first + i < A.n := by dsimp only [i]; omega
    have hreadB : y.mem (A.bc + A.b * A.n + A.first + i) =
        Signed.encode (BC A.b (A.first + i)) := by
      rw [ymem]
      simpa only [Nat.add_assoc] using (hmem A.b hb (A.first + i) hcurrent).2.1
    have hreadA : y.mem (A.ac + A.a * A.n + A.first + i) =
        Signed.encode (AC A.a (A.first + i)) := by
      rw [ymem]
      simpa only [Nat.add_assoc] using (hmem A.a ha (A.first + i) hcurrent).2.2
    have habmag := (hmag A.a ha A.b hb).1
    have hbcmag := (hmag A.b hb (A.first + i) hcurrent).2.1
    have hU2 : U ≤ 2 * U := Nat.le_mul_of_pos_left U Nat.zero_lt_two
    have habfit := hU.of_natAbs_le (habmag.trans hU2)
    have hbcfit := hU.of_natAbs_le (hbcmag.trans hU2)
    have hacfit := hU.of_natAbs_le ((hmag A.a ha (A.first + i) hcurrent).2.2.trans hU2)
    have hsumfit := hU.of_natAbs_le
      ((Int.natAbs_add_le (AB A.a A.b) (BC A.b (A.first + i))).trans (by omega))
    have hinc : Fits (w + 2) (i + 1) := hfit.of_le (by
      dsimp only [Args.addressBound, i]; omega)
    have hpos : Fits (w + 2) (A.first + i) := hfit.of_le (by
      dsimp only [Args.addressBound]; omega)
    refine WP.exists_execWithin ?_
    unfold step finishVertex
    refine WP.seq ?_
    wram_call (exec_testVertex y yrowB yrowA rfl ywab hreadB hreadA
      (hfit.of_le (by dsimp only [Args.addressBound]; omega))
      habfit hbcfit hacfit hsumfit) with b ⟨bsum, bmem, bmeta⟩
    change b.regs Signed.result = Signed.encode (total (A.first + i)) at bsum
    have bone : b.regs Reg.one = 1 := by regs_frame
    have bzero : b.regs Reg.zero = 0 := by regs_frame
    have bfirst : b.regs Reg.first = A.first :=
      (bmeta _ (by decide) (by decide)).trans yargs.2.2.2.2.2.2.1
    have bindex : b.regs Reg.index = i := bmeta _ (by decide) (by decide)
    have bfound : b.regs Reg.found = y.regs Reg.found := bmeta _ (by decide) (by decide)
    have bwit : b.regs Reg.witness = y.regs Reg.witness := bmeta _ (by decide) (by decide)
    have hreg (j : Fin 32) (hj : 9 ≤ j.val) (hj' : j.val < 17) :
        j ≠ Reg.found ∧ j ≠ Reg.witness ∧ j ≠ Reg.index ∧ b.regs j = y.regs j := by
      refine ⟨?_, ?_, ?_, bmeta j hj ?_⟩
      all_goals
        rintro rfl
        exact absurd hj' (by decide)
    wram_exec [bone, bzero, bfirst, bindex, bfound, bwit]
    all_goals refine ⟨⟨args_of_eq A yargs fun j hj hj' => ?_, bmem.trans ymem,
      by wram_simp [bone], by wram_simp [bzero],
      by wram_simp; exact (bmeta _ (by decide) (by decide)).trans yrowB,
      by wram_simp; exact (bmeta _ (by decide) (by decide)).trans yrowA,
      by wram_simp; exact (bmeta _ (by decide) (by decide)).trans ywab,
      by wram_simp; dsimp only [i]; omega, ?_, ?_, ?_⟩, by wram_simp; dsimp only [i]; omega⟩
    · obtain ⟨h1, h2, h3, hbm⟩ := hreg j hj hj'
      wram_simp [h1, h2, h3, hbm]
    · wram_simp; trivial
    · wram_simp
      exact ⟨fun _ => ⟨i, by omega, Signed.encode_injective (bsum.symm.trans hc)⟩, fun _ => trivial⟩
    · intro _; wram_simp
      exact ⟨by omega, by omega, Signed.encode_injective (bsum.symm.trans hc)⟩
    · obtain ⟨_, h2, h3, hbm⟩ := hreg j hj hj'
      wram_simp [h2, h3, hbm]
    · wram_simp [bfound]; exact yflag
    · wram_simp [bfound]; rw [yiff]
      refine ⟨fun ⟨j, hj, hzero⟩ => ⟨j, by dsimp only [i]; omega, hzero⟩,
        fun ⟨j, hj, hzero⟩ => ⟨j, ?_, hzero⟩⟩
      have hz : total (A.first + i) ≠ 0 := fun h => hc (bsum.trans (by rw [h]; rfl))
      have hne : j ≠ i := fun he => hz (he ▸ hzero)
      dsimp only [i] at *; omega
    · intro hfound
      wram_simp [bfound] at hfound
      obtain ⟨hlo, hhi, hzero⟩ := ywit hfound
      wram_simp
      exact ⟨hlo, by dsimp only [i]; omega, hzero⟩
  obtain ⟨y, hloop, hy, hdone⟩ := ExecWithin.loop_invariant I
    (fun y => A.length - y.regs Reg.index) hbody hstart
  obtain ⟨yargs, ymem, yone, yzero, yrowB, yrowA, ywab, yindex, yflag, yiff, ywit⟩ := hy
  have ylen : y.regs Reg.length = A.length := yargs.2.2.2.2.2.2.2
  have yend : y.regs Reg.index = A.length := by
    simp only [Cond.holds_lt, ylen] at hdone
    omega
  rw [yend] at yiff ywit
  refine ⟨y, (hs.seq hloop).mono (by rw [sindex]; omega), yargs, ymem, yflag,
    ⟨fun hfound => ?_, fun ⟨c, hlo, hhi, hz⟩ =>
      yiff.mpr ⟨c - A.first, Nat.sub_lt_left_of_lt_add hlo hhi,
        (Nat.add_sub_of_le hlo).symm ▸ hz⟩⟩, ywit⟩
  obtain ⟨j, hj, hz⟩ := yiff.mp hfound
  exact ⟨A.first + j, Nat.le_add_right _ _, Nat.add_lt_add_left hj _, hz⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan
