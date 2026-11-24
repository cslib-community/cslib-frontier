/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Program
public import CslibFrontier.Foundations.Data.Nat.Morton
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Tactic.UpdateSimp

/-!
# Computed native Morton spread table

The table may start dirty. Each entry is read only after an earlier native iteration has
written it, and its value follows the existing digit recurrence. Every division, remainder,
index calculation, load, store and loop instruction is charged. This is an internal stage
execution API; the complete counter must derive its constants, padded side and fit premises.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Only the scan and arithmetic/address temporaries change while constructing the table. -/
@[expose] def SpreadLocal (i : Fin 128) : Prop :=
  i = Reg.index ∨ i = Reg.address ∨ i = Reg.temporary ∨ i = Reg.position

instance (i : Fin 128) : Decidable (SpreadLocal i) :=
  inferInstanceAs (Decidable
    (i = Reg.index ∨ i = Reg.address ∨ i = Reg.temporary ∨ i = Reg.position))

/-- Construct all `2^k` actual spread words in at most `11*(2^k-1)+5` instructions,
preserving the caller memory outside exactly that table. -/
theorem exec_spreadTable {w k : ℕ} (x : Data 128)
    (hside : x.regs Reg.paddedSide = 2 ^ k)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1)
    (h2 : x.regs Reg.two = 2) (h4 : x.regs Reg.four = 4)
    (hw : Fits w (x.regs Reg.spread + 4 ^ k + 2 ^ k + 8)) :
    ∃ y, ExecWithin w spreadTable x y (11 * (2 ^ k - 1) + 5) ∧
      (∀ j < 2 ^ k, y.mem (x.regs Reg.spread + j) = Nat.Morton.spread j) ∧
      (∀ a, a < x.regs Reg.spread ∨ x.regs Reg.spread + 2 ^ k ≤ a → y.mem a = x.mem a) ∧
      ∀ i, ¬SpreadLocal i → y.regs i = x.regs i := by
  have hpow : 0 < 4 ^ k := by positivity
  have hsidePos : 0 < 2 ^ k := by positivity
  let I (y : Data 128) : Prop :=
    (∀ i, ¬SpreadLocal i → y.regs i = x.regs i) ∧
    1 ≤ y.regs Reg.index ∧ y.regs Reg.index ≤ 2 ^ k ∧
    (∀ j < y.regs Reg.index, y.mem (x.regs Reg.spread + j) = Nat.Morton.spread j) ∧
    ∀ a, ¬(x.regs Reg.spread ≤ a ∧ a < x.regs Reg.spread + y.regs Reg.index) →
      y.mem a = x.mem a
  have hbody (y : Data 128) (hy : I y) (hc : (Cond.lt Reg.index Reg.paddedSide).Holds y) :
      ∃ z, ExecWithin w spreadStep y z 9 ∧ I z ∧
        2 ^ k - z.regs Reg.index < 2 ^ k - y.regs Reg.index := by
    obtain ⟨hr, hlo, hhi, hv, hf⟩ := hy
    have hs := (hr Reg.paddedSide (by decide)).trans hside
    have hi : y.regs Reg.index < 2 ^ k := by simpa only [Cond.holds_lt, hs] using hc
    have hbase := hr Reg.spread (by decide)
    have hy1 := (hr Reg.one (by decide)).trans h1
    have hy2 := (hr Reg.two (by decide)).trans h2
    have hy4 := (hr Reg.four (by decide)).trans h4
    have hread : y.mem (x.regs Reg.spread + y.regs Reg.index / 2) =
        Nat.Morton.spread (y.regs Reg.index / 2) := hv _ (by omega)
    have hvalue := Nat.Morton.spread_lt hi
    have hquot : y.regs Reg.index / 2 ≤ y.regs Reg.index := Nat.div_le_self ..
    have hrem : y.regs Reg.index % 2 < 2 := Nat.mod_lt _ (by decide)
    have hrec : Nat.Morton.spread (y.regs Reg.index / 2) * 4 + y.regs Reg.index % 2 =
        Nat.Morton.spread (y.regs Reg.index) := by
      rw [Nat.Morton.spread_eq (y.regs Reg.index)]; omega
    unfold spreadStep
    wram_exec [hy1, hy2, hy4, hbase, hread, hrec]
    refine ⟨⟨?_, by wram_simp, by wram_simp; omega, ?_, ?_⟩, by wram_simp; omega⟩
    · intro i hni
      have hne : i ≠ Reg.index ∧ i ≠ Reg.address ∧ i ≠ Reg.temporary ∧ i ≠ Reg.position := by
        simpa only [SpreadLocal, not_or] using hni
      wram_simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2, hr i hni]
    · intro j hj; wram_simp at hj ⊢
      by_cases he : j = y.regs Reg.index
      · subst j; update_simp
      · update_simp; exact hv j (by omega)
    · intro a ha; wram_simp at ha ⊢; update_simp; exact hf a (by omega)
  refine WP.exists_execWithin ?_
  unfold spreadTable spreadSetup
  wram_exec [h0]
  wram_call (ExecWithin.loop_invariant I (fun y => 2 ^ k - y.regs Reg.index) hbody
    ⟨fun i hi => by
      have hi' : i ≠ Reg.address ∧ i ≠ Reg.index := by simp only [SpreadLocal, not_or] at hi; tauto
      wram_simp [hi'.1, hi'.2],
     by wram_simp, by wram_simp; omega,
     fun j hj => by
       wram_simp at hj; obtain rfl : j = 0 := by omega
       wram_simp [Nat.Morton.spread_zero],
     fun a ha => by wram_simp at ha; update_simp⟩)
    with z ⟨⟨hr, hlo, hhi, hv, hf⟩, hstop⟩
  have hi : z.regs Reg.index = 2 ^ k := by
    have hs := (hr Reg.paddedSide (by decide)).trans hside
    simp only [Cond.holds_lt, hs] at hstop; omega
  exact ⟨by wram_simp; omega, by simpa only [hi] using hv,
    fun a ha => hf a (by omega), hr⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
