/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Program
import CslibFrontier.Computability.WordRAM.Record
import CslibFrontier.Computability.WordRAM.RegisterFrame

/-!
# Actual native parameter computation from the original dimension

The original scalar n derives every logarithm, power and arithmetic fit. The actual calls
and all setup/copy/branch instructions are charged. No exponent, logarithm, power, parameter
table or execution certificate is an input to the public rule.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters

open Cslib.WordRAM
open Cslib.Algorithms.ExactTriangle

/-- Original-scalar word envelope, including all fixed constants and both power calls. -/
@[expose] def wordBudget (n : ℕ) : ℕ := 2394 + 32 * (n + 1)

/-- Charged complete caller computation, before the final halt. -/
@[expose] def timeBound (n : ℕ) : ℕ :=
  4 * Nat.log 2 n + 8 * ParameterChoice.blocks n + 4 * ParameterChoice.level n + 33

private def Ready (n : ℕ) (x : Data 16) : Prop := x.regs Reg.side = n ∧
  x.regs Reg.blocks = ParameterChoice.blocks n ∧ x.regs Reg.level = ParameterChoice.level n ∧
  x.regs Reg.tensorDepth = ParameterChoice.tensorDepth n ∧ x.regs Reg.four = 4

private theorem offset7_injective {r : ℕ} {f : Fin r → Fin 16}
    (hf : ∀ i, (f i).val = i.val + 7) : Function.Injective f := by
  intro i j h
  exact Fin.ext (Nat.add_right_cancel ((hf i).symm.trans ((congrArg Fin.val h).trans (hf j))))

private theorem offset7_preserves {r : ℕ} (c : Code .standard r) (f : Fin r → Fin 16)
    (hf : ∀ i, (f i).val = i.val + 7) (i : Fin 16) (hi : i.val < 7 ∨ 7 + r ≤ i.val) :
    (c.rename f).Preserves i :=
  c.preserves_rename_of_offset f (fun j => (hf j).trans (Nat.add_comm j.val 7)) i hi

private theorem power_preserves (i : Fin 16) (hi : i.val < 7 ∨ 12 ≤ i.val) :
    (Power.program.rename powerRegisters).Preserves i :=
  offset7_preserves Power.program powerRegisters (fun _ => rfl) i hi

private theorem Ready.of_frame {n : ℕ} {x y : Data 16} (hx : Ready n x)
    (h : ∀ i : Fin 16, i = Reg.side ∨ i = Reg.blocks ∨ i = Reg.level ∨
      i = Reg.tensorDepth ∨ i = Reg.four → y.regs i = x.regs i) : Ready n y :=
  ⟨(h Reg.side (by decide)).trans hx.1,
    (h Reg.blocks (by decide)).trans hx.2.1,
    (h Reg.level (by decide)).trans hx.2.2.1,
    (h Reg.tensorDepth (by decide)).trans hx.2.2.2.1,
    (h Reg.four (by decide)).trans hx.2.2.2.2⟩

private theorem Ready.after_power {w n : ℕ} {x y : Data 16} {t : ℕ}
    (hx : Ready n x) (he : ExecWithin w (Power.program.rename powerRegisters) x y t) :
    Ready n y :=
  hx.of_frame fun i hi => he.regs_eq (power_preserves i (by
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide))

private theorem finish_preserves : ∀ i : Fin 16,
    i ≠ Reg.window → i ≠ Reg.fast → finish.Preserves i := by decide

private theorem exec_finish {w n : ℕ} (x : Data 16)
    (hb : x.regs Reg.blocks = ParameterChoice.blocks n)
    (hv : x.regs Reg.workValue = ParameterChoice.window n)
    (hf : Fits w (wordBudget n)) :
    ∃ y, ExecWithin w finish x y 5 ∧ y.regs Reg.window = ParameterChoice.window n ∧
      y.regs Reg.fast = (if 0 < ParameterChoice.blocks n then 1 else 0) ∧ y.mem = x.mem ∧
      ∀ i, i ≠ Reg.window → i ≠ Reg.fast → y.regs i = x.regs i := by
  dsimp only [wordBudget] at hf
  refine WP.exists_execWithin_preserves (P := fun i => i ≠ Reg.window ∧ i ≠ Reg.fast)
    (fun i hi => finish_preserves i hi.1 hi.2) ?_
  wram_exec [finish, hb, hv]
  all_goals exact fun hpres =>
    ⟨by wram_simp, by wram_simp [hc], rfl, fun i hw hfast => hpres i ⟨hw, hfast⟩⟩

/-- Computed dyadic parameters, original dimension and unchanged memory. -/
@[expose] def Post (n : ℕ) (x y : Data 16) : Prop :=
  y.regs Reg.side = n ∧ y.regs Reg.blocks = ParameterChoice.blocks n ∧
  y.regs Reg.level = ParameterChoice.level n ∧ y.regs Reg.window =
    ParameterChoice.window n ∧
  y.regs Reg.groups = ParameterChoice.groups n ∧
  y.regs Reg.tensorDepth = ParameterChoice.tensorDepth n ∧
  y.regs Reg.fast = (if 0 < ParameterChoice.blocks n then 1 else 0) ∧ y.mem = x.mem

/-- Execute the logarithm, rounded exponent arithmetic, two real powers and regime flag.
Memory and the original n are preserved. All fits follow from one original-scalar envelope. -/
theorem exec {w n : ℕ} (x : Data 16) (hn : x.regs Reg.side = n)
    (hfit : Fits w (wordBudget n)) :
    ∃ y, ExecWithin w program x y (timeBound n) ∧ Post n x y := by
  unfold Post
  have ht : ParameterChoice.blocks n ≤ n :=
    (ParameterChoice.blocks_le_log n).trans (Nat.log_le_self 2 n)
  have hm : ParameterChoice.level n ≤ n :=
    (ParameterChoice.level_le_log n).trans (Nat.log_le_self 2 n)
  have hL : ParameterChoice.tensorDepth n ≤ 21 * n := Nat.mul_le_mul_left 21 hm
  have hg := (ParameterChoice.powers_le n).1
  have hD := (ParameterChoice.powers_le n).2
  have hlog := Nat.log_le_self 2 n
  have hfit' : Fits w (2394 + 32 * (n + 1)) := hfit
  have hblocks_eq : Nat.log 2 n / 2394 = ParameterChoice.blocks n := rfl
  have hlevel_eq : 63 * ParameterChoice.blocks n = ParameterChoice.level n := rfl
  have hdepth_eq : 21 * ParameterChoice.level n = ParameterChoice.tensorDepth n := rfl
  have hpg : Fits w (4 ^ (2 * ParameterChoice.blocks n) + 2 * ParameterChoice.blocks n + 2) :=
    hfit'.of_le (by change ParameterChoice.groups n + 2 * ParameterChoice.blocks n + 2 ≤ _; omega)
  have hpD : Fits w (4 ^ ParameterChoice.level n + ParameterChoice.level n + 2) :=
    hfit'.of_le (by change ParameterChoice.window n + ParameterChoice.level n + 2 ≤ _; omega)
  have log_inj : Function.Injective logRegisters := offset7_injective (fun _ => rfl)
  have pow_inj : Function.Injective powerRegisters := offset7_injective (fun _ => rfl)
  let a := x.set Reg.workValue n
  have copy : ExecWithin (B := .standard) w (ram[ Reg.workValue ← Reg.side ]) x a 1 := by
    simpa only [hn] using ExecWithin.copy (w := w) (x := x) (d := Reg.workValue) (s := Reg.side)
  obtain ⟨b, hb, blog, bmem, _, _⟩ := NatLog.exec_rename (w := w) logRegisters log_inj a
    (by fits) (by change Fits w n; fits) (by change Fits w (Nat.log 2 n + 1); fits)
  have bside : b.regs Reg.side = n :=
    (hb.regs_eq (offset7_preserves NatLog.program logRegisters (fun _ => rfl) Reg.side
      (by decide))).trans hn
  have blog' : b.regs Reg.workCount = Nat.log 2 n := blog
  obtain ⟨c, prep, cReady, cBase, cExp, cmem⟩ :
      ∃ c, ExecWithin w prepare b c 9 ∧ Ready n c ∧
        c.regs (powerRegisters Power.base) = 4 ∧
        c.regs (powerRegisters Power.exponent) = 2 * ParameterChoice.blocks n ∧
        c.mem = b.mem := by
    refine WP.exists_execWithin ?_
    unfold prepare Ready
    wram_exec [blog', hblocks_eq, hlevel_eq, hdepth_eq]
    wram_simp [bside]
    omega
  obtain ⟨d, hd, dg, _, _, dmem, _, _, _⟩ := Power.exec_rename powerRegisters pow_inj
    4 (2 * ParameterChoice.blocks n) (by decide) c cBase cExp hpg
  have dReady := cReady.after_power hd
  have dg' : d.regs Reg.workValue = ParameterChoice.groups n := dg
  obtain ⟨e, next, eReady, eBase, eExp, eg, emem⟩ :
      ∃ e, ExecWithin w nextPower d e 3 ∧ Ready n e ∧
        e.regs (powerRegisters Power.base) = 4 ∧
        e.regs (powerRegisters Power.exponent) = ParameterChoice.level n ∧
        e.regs Reg.groups = ParameterChoice.groups n ∧
        e.mem = d.mem := by
    refine WP.exists_execWithin ?_
    unfold nextPower Ready
    wram_exec [dg', dReady.2.2.1, dReady.2.2.2.2]
    wram_simp [dReady.1, dReady.2.1, dReady.2.2.1, dReady.2.2.2.1, dReady.2.2.2.2]
  obtain ⟨f, hf, fD, _, _, fmem, _, _, _⟩ := Power.exec_rename powerRegisters pow_inj
    4 (ParameterChoice.level n) (by decide) e eBase eExp hpD
  have fReady := eReady.after_power hf
  have fg : f.regs Reg.groups = ParameterChoice.groups n :=
    (hf.regs_eq (power_preserves Reg.groups (by decide))).trans eg
  obtain ⟨y, hy, yD, yflag, ymem, yr⟩ := exec_finish f fReady.2.1 fD hfit
  have yReady : Ready n y := fReady.of_frame fun i hi => by
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact yr _ (by decide) (by decide)
  have full := copy.seq (hb.seq (prep.seq (hd.seq (next.seq (hf.seq hy)))))
  refine ⟨y, full.mono ?_, yReady.1, yReady.2.1, yReady.2.2.1, yD,
    (yr Reg.groups (by decide) (by decide)).trans fg, yReady.2.2.2.1, yflag,
    ymem.trans (fmem.trans (emem.trans (dmem.trans (cmem.trans bmem))))⟩
  rw [show a.regs (logRegisters NatLog.arg) = n from rfl, timeBound]
  omega

/-- Actual execution is logarithmic, even using conservative bounds for both power calls. -/
theorem timeBound_le (n : ℕ) : timeBound n ≤ 16 * Nat.log 2 n + 33 := by
  have ht := ParameterChoice.blocks_le_log n
  have hm := ParameterChoice.level_le_log n
  unfold timeBound
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters
