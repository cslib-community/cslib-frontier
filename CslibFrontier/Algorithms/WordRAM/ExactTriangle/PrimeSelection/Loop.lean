/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Step
public import CslibFrontier.Foundations.NumberTheory.SqrtPrimeWindow
import all CslibFrontier.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Step
import Mathlib.Data.Nat.Sqrt
import CslibFrontier.Computability.WordRAM.Record
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Native selection loop composed with a finite counting call

`exec_of_count` is a component composition rule. It derives actual selection execution,
minimum correctness, a complete controller bound and register preservation from the explicitly
stated execution law for the supplied finite counting code. The law also preserves a memory
predicate, allowing original matrices and a caller frame to persist across dirty workspace
reuse. `PrimeSelection.Exec` discharges that law using the actual modular counter; this
component rule alone does not assume a completed algorithm or complexity result.

The invariant `BestBefore` of `PrimeSelection.Minimum` and the step rule
`exec_candidate_bestBefore` of `PrimeSelection.Step` are private proof plumbing of the selector;
this module reads both through `import all` of `PrimeSelection.Step`, which itself reads
`PrimeSelection.Minimum` through `import all`.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

/-- Compose the real selector with an explicitly certified finite counting call. `T` bounds
that call including its six argument copies. There is no supplied prime list. The
concrete-counter instantiation is proved separately in `PrimeSelection.Exec`. -/
theorem exec_of_count {w D T : ℕ} (counter : Code .standard 128) (score : ℕ → ℕ)
    (Source : (ℕ → ℕ) → Prop) (x : Data 160) (hD : 4 ≤ D)
    (hne : (Nat.sqrtPrimeWindow D).Nonempty) (hxD : x.regs Reg.window = D)
    (hfit : Fits w (4 * (D + 2) * (D + 2) + 4)) (hx : Source x.mem)
    (hcount : ∀ z, Source z.mem →
      (∀ i, 131 ≤ i.val ∧ i.val ≤ 136 → z.regs i = x.regs i) →
      z.regs Reg.cursor ∈ Nat.sqrtPrimeWindow D →
      ∃ a, ExecWithin w (count counter) z a T ∧
        a.regs Reg.countResult = score (z.regs Reg.cursor) ∧ Source a.mem) :
    ∃ y, ExecWithin w (program counter) x y
        ((Nat.sqrt D + 1) * (T + 7 * Nat.sqrt D + 20) + 10) ∧
      y.regs Reg.found = 1 ∧
      y.regs Reg.best ∈ Nat.sqrtPrimeWindow D ∧
      y.regs Reg.bestCount = score (y.regs Reg.best) ∧
      (∀ p ∈ Nat.sqrtPrimeWindow D, score (y.regs Reg.best) ≤ score p) ∧ Source y.mem ∧
      ∀ i, (131 ≤ i.val ∧ i.val ≤ 136) ∨ 143 ≤ i.val → y.regs i = x.regs i := by
  let I (y : Data 160) : Prop :=
    (∀ i, 131 ≤ i.val ∧ i.val ≤ 136 → y.regs i = x.regs i) ∧
      y.regs Reg.one = 1 ∧ y.regs Reg.zero = 0 ∧ y.regs Reg.four = 4 ∧
      2 ≤ y.regs Reg.cursor ∧ y.regs Reg.cursor ≤ Nat.sqrt D + 1 ∧
      y.regs Reg.square = y.regs Reg.cursor * y.regs Reg.cursor ∧
      BestBefore D score (y.regs Reg.cursor) (y.regs Reg.best)
        (y.regs Reg.bestCount) (y.regs Reg.found) ∧ Source y.mem
  have hbody (y : Data 160) (hy : I y) (hc : (Cond.lt Reg.square Reg.window).Holds y) :
      ∃ z, ExecWithin w (body counter) y z (T + 7 * Nat.sqrt D + 18) ∧ I z ∧
        Nat.sqrt D + 1 - z.regs Reg.cursor < Nat.sqrt D + 1 - y.regs Reg.cursor := by
    obtain ⟨hstatic, ho, hz, hf, hk2, hkmax, hsq, hbest, hSource⟩ := hy
    have hyD : y.regs Reg.window = D := by regs_frame
    have hupper : y.regs Reg.cursor * y.regs Reg.cursor < D := by
      simpa only [Cond.holds_lt, hsq, hyD] using hc
    have hk : y.regs Reg.cursor ≤ Nat.sqrt D := Nat.le_sqrt.2 hupper.le
    have hkD : y.regs Reg.cursor ≤ D := hk.trans (Nat.sqrt_le_self D)
    have hsquare : y.regs Reg.cursor * y.regs Reg.cursor ≤ (D + 2) * (D + 2) :=
      Nat.mul_self_le_mul_self (by omega)
    have hnew : (y.regs Reg.cursor + 1) * (y.regs Reg.cursor + 1) ≤ (D + 2) * (D + 2) :=
      Nat.mul_self_le_mul_self (by omega)
    have hfourFit : Fits w (4 * (y.regs Reg.cursor * y.regs Reg.cursor)) := hfit.of_le (by
      have hm := Nat.mul_le_mul_left 4 hsquare
      simpa only [Nat.mul_assoc] using hm.trans (Nat.le_add_right _ _))
    have hnewFit : Fits w ((y.regs Reg.cursor + 1) * (y.regs Reg.cursor + 1)) :=
      hfit.of_le (by rw [Nat.mul_assoc]; omega)
    have htrialFit : Fits w (y.regs Reg.cursor + 2) := hfit.of_le (by
      have hsmall : D + 2 ≤ (D + 2) * (D + 2) := by
        simpa only [Nat.mul_one] using
          Nat.mul_le_mul_left (D + 2) (show 1 ≤ D + 2 by omega)
      rw [Nat.mul_assoc]
      omega)
    let u := y.set Reg.fourSquare (4 * (y.regs Reg.cursor * y.regs Reg.cursor))
    have hprep : ExecWithin w (ram[ Reg.fourSquare ← Reg.four * Reg.square ]) y u 1 := by
      wram_exec [hf, hsq]
    have huk : u.regs Reg.cursor = y.regs Reg.cursor := by
      simp +decide [u, Reg.cursor, Reg.fourSquare]
    have huStatic : ∀ i, 131 ≤ i.val ∧ i.val ≤ 136 → u.regs i = x.regs i := fun i hi => by
      have hne : i ≠ Reg.fourSquare := fun h => by subst h; exact absurd hi (by decide)
      simp only [u, Data.set_regs, Function.update_of_ne hne, hstatic i hi]
    obtain ⟨v, hv, hvbest, hvSource, hvr⟩ := exec_candidate_bestBefore counter score Source u
      (by simpa +decide [u, Reg.zero, Reg.fourSquare] using hz)
      (by simpa +decide [u, Reg.one, Reg.fourSquare] using ho)
      (by regs_frame) (by simpa only [huk] using hk2)
      (by simpa only [huk] using hupper) (by simp [u, huk])
      (by simpa only [huk] using htrialFit) hSource
      (by simpa +decide [u, Reg.cursor, Reg.best, Reg.bestCount, Reg.found, Reg.fourSquare]
        using hbest)
      (by
        intro a ha hmeta hwindow
        obtain ⟨b, hb, hbscore, hbSource⟩ := hcount a ha
          (fun i hi => (hmeta i (by omega)).trans (huStatic i hi))
          (by simpa only [hmeta Reg.cursor (by decide)] using hwindow)
        exact ⟨b, hb, by simpa only [hmeta Reg.cursor (by decide)] using hbscore, hbSource⟩)
    have hvk : v.regs Reg.cursor = y.regs Reg.cursor := by regs_frame
    have hvone : v.regs Reg.one = 1 := by regs_frame
    obtain ⟨z, hzrun, hzk, hzsq, hzm, hzr⟩ := exec_advance v hvone
      (by simpa only [hvk] using hnewFit)
    have hzk' : z.regs Reg.cursor = y.regs Reg.cursor + 1 := by simpa only [hvk] using hzk
    have he : ExecWithin w (body counter) y z (T + 7 * Nat.sqrt D + 18) :=
      (hprep.seq (hv.seq hzrun)).mono (by rw [huk]; omega)
    refine ⟨z, he, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        exact (he.regs_eq ((preserves_input counter i (Or.inl hi)).2)).trans (hstatic i hi)
      · regs_frame
      · regs_frame
      · regs_frame
      · rw [hzk']; omega
      · rw [hzk']; omega
      · simpa only [hvk, hzk'] using hzsq
      · rw [hzk']
        simpa only [huk, hzr Reg.best (by decide) (by decide),
          hzr Reg.bestCount (by decide) (by decide), hzr Reg.found (by decide) (by decide)]
          using hvbest
      · simpa only [hzm] using hvSource
    · rw [hzk']; omega
  refine WP.exists_execWithin_preserves
    (P := fun i => (131 ≤ i.val ∧ i.val ≤ 136) ∨ 143 ≤ i.val)
    (fun i hi => preserves_input counter i hi) ?_
  unfold program setup
  have hroot : 2 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by simpa using hD)
  wram_exec
  wram_call (ExecWithin.loop_invariant I (fun y => Nat.sqrt D + 1 - y.regs Reg.cursor) hbody
    ⟨fun i hi => by
      have hne : i ≠ Reg.one ∧ i ≠ Reg.zero ∧ i ≠ Reg.four ∧ i ≠ Reg.cursor ∧ i ≠ Reg.square ∧
          i ≠ Reg.best ∧ i ≠ Reg.bestCount ∧ i ≠ Reg.found := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (intro h; subst h; exact absurd hi (by decide))
      wram_simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1,
        hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2],
     by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp; omega,
     by wram_simp, by wram_simp; exact bestBefore_initial D score, hx⟩)
    with y ⟨⟨hstatic, _, _, _, _, _, hsq, hbest, hSource⟩, hstop⟩
  have hDy : y.regs Reg.window = D := by regs_frame
  have hstop' : D ≤ y.regs Reg.cursor * y.regs Reg.cursor := by
    simpa only [Cond.holds_lt, hsq, hDy, not_lt] using hstop
  obtain ⟨hfound, hwindow, hvalue, hminimum⟩ := bestBefore_exit hbest hne hstop'
  refine ⟨?_, fun hpres => ⟨hfound, hwindow, hvalue,
    by simpa only [hvalue] using hminimum, hSource, fun i hi => hpres i hi⟩⟩
  wram_simp
  have hm := Nat.mul_le_mul_right (T + 7 * Nat.sqrt D + 20) (Nat.sub_le (Nat.sqrt D + 1) 2)
  have hcost : T + 7 * Nat.sqrt D + 18 + 2 = T + 7 * Nat.sqrt D + 20 := by omega
  rw [hcost]; omega

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
