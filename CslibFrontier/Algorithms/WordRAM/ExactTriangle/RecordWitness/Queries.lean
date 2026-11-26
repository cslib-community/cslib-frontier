/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Step
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Trace

/-!
# The actual short-circuit query loop

The proof derives its scan trace from the original answer words and the verifier's integer
equation. Runtime execution receives neither trace nor witness function. Variable-cost loop
accounting charges a complete scan exactly when the native controller actually invokes it.
The finite scan bound follows the counting argument of pinned `ScanPairs.lean`;
the native code, ABI and instruction constants are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

private theorem potential_step (active : ℕ → Prop) [DecidablePred active]
    {i Q T : ℕ} (hi : i < Q) :
    (if active i then T + 6 else 6) + 2 +
        (8 * (Q - (i + 1)) + T * (Nat.count active Q - Nat.count active (i + 1))) ≤
      8 * (Q - i) + T * (Nat.count active Q - Nat.count active i) := by
  have hle : Nat.count active (i + 1) ≤ Nat.count active Q :=
    Nat.count_monotone active (Nat.succ_le_of_lt hi)
  rw [show Q - i = Q - (i + 1) + 1 by omega, Nat.mul_add]
  by_cases h : active i
  · rw [ite_eq_left h]
    rw [Nat.count_succ, ite_eq_left h] at hle ⊢
    rw [show Nat.count active Q - Nat.count active i =
      (Nat.count active Q - (Nat.count active i + 1)) + 1 by omega, Nat.mul_add]
    omega
  · simp only [ite_eq_right h, Nat.count_succ, Nat.add_zero]
    omega

/-- Run the actual answer/query loop. Every query coordinate is read from the protected
interleaved block, and every success is verified against the original three integer arrays.
Only accepted pairs without an original witness contribute to the failure count. -/
theorem exec_queries {w U n first length out queries Q : ℕ}
    (AB BC AC : ℕ → ℕ → ℤ) (a b : ℕ → ℕ) (x : Data 400)
    (hx : Fixed n first length out queries Q x)
    (hi : x.regs Reg.index = 0) (hs : x.regs Reg.scans = 0)
    (hf : x.regs Reg.found = 0)
    (hquery : ∀ i < Q, x.mem (queries + 2 * i) = a i ∧
      x.mem (queries + 2 * i + 1) = b i ∧ a i < n ∧ b i < n)
    (hc : first + length ≤ n)
    (hmem : ∀ u < n, ∀ v < n,
      x.mem (5 + (u * n + v)) = Signed.encode (AB u v) ∧
      x.mem (5 + n * n + (u * n + v)) = Signed.encode (BC u v) ∧
      x.mem (5 + n * n + n * n + (u * n + v)) = Signed.encode (AC u v))
    (hmag : ∀ u < n, ∀ v < n,
      (AB u v).natAbs ≤ U ∧ (BC u v).natAbs ≤ U ∧ (AC u v).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2)
      (out + queries + 4 * Q + 6 * (n * n) + n + first + length + 64)) :
    ∃ y S, ExecWithin (w + 2) (.loop (.lt Reg.index Reg.count) step) x y
        (8 * Q + (42 * length + 28) * S + 2) ∧
      Fixed n first length out queries Q y ∧ y.mem = x.mem ∧
      y.regs Reg.index = Q ∧ y.regs Reg.scans = S ∧
      S ≤ Nat.count (fun i => x.mem (out + i) ≠ 0 ∧
        ∀ c : Fin length, AB (a i) (b i) + BC (b i) (first + c.val) +
          AC (a i) (first + c.val) ≠ 0) Q + y.regs Reg.found ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      (y.regs Reg.found = 1 ↔ ∃ i < Q, x.mem (out + i) ≠ 0 ∧
        ∃ c, first ≤ c ∧ c < first + length ∧ AB (a i) (b i) + BC (b i) c + AC (a i) c = 0) ∧
      (y.regs Reg.found = 1 → ∃ i < Q,
        x.mem (out + i) ≠ 0 ∧ y.regs Reg.witnessA = a i ∧ y.regs Reg.witnessB = b i ∧
        first ≤ y.regs Reg.witnessC ∧ y.regs Reg.witnessC < first + length ∧
        AB (a i) (b i) + BC (b i) (y.regs Reg.witnessC) +
          AC (a i) (y.regs Reg.witnessC) = 0) := by
  let accept (i : ℕ) : Bool := decide (x.mem (out + i) ≠ 0)
  let hit (i : ℕ) : Bool := decide (∃ c : Fin length,
    AB (a i) (b i) + BC (b i) (first + c.val) + AC (a i) (first + c.val) = 0)
  let active (i : ℕ) : Prop := (accept i && !foundBefore accept hit i) = true
  have hit_iff (i : ℕ) : hit i = true ↔ ∃ c, first ≤ c ∧ c < first + length ∧
      AB (a i) (b i) + BC (b i) c + AC (a i) c = 0 := by
    simp only [hit, decide_eq_true_eq]
    exact ⟨fun ⟨c, hz⟩ => ⟨first + c.val, by omega, by omega, hz⟩,
      fun ⟨c, hlo, hhi, hz⟩ =>
        ⟨⟨c - first, by omega⟩, by simpa only [Nat.add_sub_of_le hlo] using hz⟩⟩
  let I (y : Data 400) : Prop :=
    Fixed n first length out queries Q y ∧ y.mem = x.mem ∧ y.regs Reg.index ≤ Q ∧
    y.regs Reg.found = (foundBefore accept hit (y.regs Reg.index)).toNat ∧
    y.regs Reg.scans = Nat.count active (y.regs Reg.index) ∧
    (y.regs Reg.found = 1 → ∃ i < y.regs Reg.index,
      x.mem (out + i) ≠ 0 ∧ y.regs Reg.witnessA = a i ∧ y.regs Reg.witnessB = b i ∧
      first ≤ y.regs Reg.witnessC ∧ y.regs Reg.witnessC < first + length ∧
      AB (a i) (b i) + BC (b i) (y.regs Reg.witnessC) +
        AC (a i) (y.regs Reg.witnessC) = 0)
  let Φ (y : Data 400) := 8 * (Q - y.regs Reg.index) +
    (42 * length + 28) * (Nat.count active Q - Nat.count active (y.regs Reg.index))
  have hstart : I x := ⟨hx, rfl, by omega,
    by simp only [hi, hf, foundBefore_zero, Bool.toNat_false],
    by simp only [hi, hs, Nat.count_zero], fun h => by omega⟩
  have body (y : Data 400) (hy : I y) (hcond : (Cond.lt Reg.index Reg.count).Holds y) :
      ∃ z T, ExecWithin (w + 2) step y z T ∧ I z ∧ T + 2 + Φ z ≤ Φ y := by
    obtain ⟨yFixed, ym, yi, yf, ys, yw⟩ := hy
    let i := y.regs Reg.index
    change y.regs Reg.found = (foundBefore accept hit i).toNat at yf
    have hilt : i < Q := by simpa only [Cond.holds_lt, yFixed.count] using hcond
    have hscans : y.regs Reg.scans ≤ Q := ys ▸ (Nat.count_le active).trans yi
    by_cases hact : active i
    · have hinfo : accept i = true ∧ foundBefore accept hit i = false := by
        simpa only [active, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false] using hact
      have hanswer : y.mem (out + i) ≠ 0 := ym ▸ of_decide_eq_true hinfo.1
      obtain ⟨haWord, hbWord, ha, hb⟩ := hquery i hilt
      obtain ⟨z, he, zFixed, zm, zi, zs, zf, zh, zw⟩ := exec_step_scan (i := i) AB BC AC y yFixed
        rfl rfl (by rw [yf, hinfo.2]; rfl) hanswer (ym ▸ haWord) (ym ▸ hbWord) ha hb hc (ym ▸ hmem)
        hmag hU (hfit.of_le (by dsimp only [i]; omega))
      have zflag : z.regs Reg.found = (hit i).toNat := by
        cases hh : hit i
        · exact zf.resolve_right fun h =>
            Bool.false_ne_true (hh ▸ (hit_iff i).mpr (zh.mp h))
        · exact zh.mpr ((hit_iff i).mp hh)
      refine ⟨z, 42 * length + 34, he, ⟨zFixed, zm.trans ym, by omega,
        by simpa only [zi, foundBefore_succ, hinfo.1, hinfo.2, Bool.true_and, Bool.false_or]
             using zflag,
        by rwa [zi, Nat.count_succ, ite_eq_left hact, ← ys],
        fun hz => let ⟨za, zb, zlo, zhi, zeq⟩ := zw hz
          ⟨i, by omega, ym ▸ hanswer, za, zb, zlo, zhi, zeq⟩⟩, ?_⟩
      simpa only [ite_eq_left hact, Φ, zi, i] using
        potential_step active (T := 42 * length + 28) hilt
    · have hskip : y.regs Reg.found ≠ 0 ∨ y.mem (out + i) = 0 := by
        by_cases hz : y.regs Reg.found = 0
        · refine Or.inr (by_contra fun hn => hact ?_)
          have hb : foundBefore accept hit i = false := Bool.toNat_eq_zero.mp (yf.symm.trans hz)
          simpa only [active, accept, hb, Bool.not_false, Bool.and_true, decide_eq_true_eq] using
            ym ▸ hn
        · exact Or.inl hz
      obtain ⟨z, he, zFixed, zm, zi, frame⟩ := exec_step_skip (i := i) y yFixed rfl hskip
        (hfit.of_le (by dsimp only [i]; omega))
      have zreg (r : Fin 400)
          (hr : r ≠ Reg.index ∧ r ≠ Reg.address ∧ r ≠ Reg.answer := by decide) :
          z.regs r = y.regs r := frame r hr.1 hr.2.1 hr.2.2
      have hnext : foundBefore accept hit (i + 1) = foundBefore accept hit i := by
        rw [foundBefore_succ]
        cases ha : accept i <;> cases hb : foundBefore accept hit i <;>
          simp_all [active]
      refine ⟨z, 6, he, ⟨zFixed, zm.trans ym, by omega,
        by rwa [zi, hnext, zreg Reg.found],
        by rwa [zi, Nat.count_succ, ite_eq_right hact, Nat.add_zero, zreg Reg.scans],
        fun hz => by
          obtain ⟨j, hj, hm, hwa, hwb, hlo, hhi, hzsum⟩ := yw ((zreg Reg.found).symm.trans hz)
          exact ⟨j, by omega, hm, (zreg Reg.witnessA).trans hwa, (zreg Reg.witnessB).trans hwb,
            zreg Reg.witnessC ▸ hlo, zreg Reg.witnessC ▸ hhi, zreg Reg.witnessC ▸ hzsum⟩⟩, ?_⟩
      simpa only [ite_eq_right hact, Φ, zi, i] using
        potential_step active (T := 42 * length + 28) hilt
  obtain ⟨y, he, ⟨yFixed, ym, yi, yf, ys, yw⟩, hend⟩ := ExecWithin.loop_potential I Φ body hstart
  have yindex : y.regs Reg.index = Q := by simp only [Cond.holds_lt, yFixed.count] at hend; omega
  have hfail : Nat.count (fun i => (accept i && !hit i) = true) Q =
      Nat.count (fun i => x.mem (out + i) ≠ 0 ∧
        ∀ c : Fin length, AB (a i) (b i) + BC (b i) (first + c.val) +
          AC (a i) (first + c.val) ≠ 0) Q := by
    congr 1 with i : 1
    simp only [accept, hit, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not, not_exists]
  refine ⟨y, Nat.count active Q,
    by simpa only [Φ, hi, Nat.sub_zero, Nat.count_zero, Nat.mul_zero, Nat.add_zero] using he,
    yFixed, ym, yindex, yindex ▸ ys,
    by rw [← hfail, yf, yindex]; exact scan_count_le accept hit Q,
    by rw [yf, yindex]; cases foundBefore accept hit Q <;> simp,
    by simp only [yf, yindex, Bool.toNat_eq_one, foundBefore_eq_true, accept, decide_eq_true_eq,
         hit_iff],
    yindex ▸ yw⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
