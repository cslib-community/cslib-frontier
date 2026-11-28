/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Pair
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged query-controller steps

An accepted step reads the actual answer word and invokes the actual original-weight verifier.
The separate skipped-step rule accounts for both zero answers and the already-successful
short circuit. These are internal execution rules, not additional algorithm inputs.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

/-- A nonzero actual product word, while still searching, causes exactly one native scan.
The six additional instructions include both branches, answer access and cursor advancement. -/
theorem exec_step_scan {w U n first length out queries count i scans a b : ℕ}
    (AB BC AC : ℕ → ℕ → ℤ) (x : Data 400)
    (hx : Fixed n first length out queries count x)
    (hi : x.regs Reg.index = i) (hs : x.regs Reg.scans = scans)
    (hf : x.regs Reg.found = 0) (hanswer : x.mem (out + i) ≠ 0)
    (haWord : x.mem (queries + 2 * i) = a)
    (hbWord : x.mem (queries + 2 * i + 1) = b)
    (ha : a < n) (hb : b < n) (hc : first + length ≤ n)
    (hmem : ∀ u < n, ∀ v < n,
      x.mem (5 + (u * n + v)) = Signed.encode (AB u v) ∧
      x.mem (5 + n * n + (u * n + v)) = Signed.encode (BC u v) ∧
      x.mem (5 + n * n + n * n + (u * n + v)) = Signed.encode (AC u v))
    (hmag : ∀ u < n, ∀ v < n,
      (AB u v).natAbs ≤ U ∧ (BC u v).natAbs ≤ U ∧ (AC u v).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2)
      (out + queries + 3 * i + scans + 6 * (n * n) + n + first + length + 40)) :
    ∃ y, ExecWithin (w + 2) step x y (42 * length + 34) ∧
      Fixed n first length out queries count y ∧ y.mem = x.mem ∧
      y.regs Reg.index = i + 1 ∧ y.regs Reg.scans = scans + 1 ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      (y.regs Reg.found = 1 ↔
        ∃ c, first ≤ c ∧ c < first + length ∧ AB a b + BC b c + AC a c = 0) ∧
      (y.regs Reg.found = 1 →
        y.regs Reg.witnessA = a ∧ y.regs Reg.witnessB = b ∧
        first ≤ y.regs Reg.witnessC ∧ y.regs Reg.witnessC < first + length ∧
        AB a b + BC b (y.regs Reg.witnessC) + AC a (y.regs Reg.witnessC) = 0) := by
  have hfit' : Fits (w + 2)
      (queries + 2 * i + scans + 6 * (n * n) + n + first + length + 32) :=
    hfit.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold step
  wram_exec [hf, hx.zero, hx.output, hi, hanswer]
  wram_call (exec_scanPair AB BC AC _
    (hx.of_frame fun j hj => by
      have haddr : j ≠ Reg.address := fun he => by
        subst j; norm_num [Reg.address, Reg.one, Reg.zero] at hj
      have hans : j ≠ Reg.answer := fun he => by
        subst j; norm_num [Reg.answer, Reg.one, Reg.zero] at hj
      wram_simp [haddr, hans])
    (by wram_simp [hi]) (by wram_simp [hs]) (by wram_simp [hf])
    haWord hbWord ha hb hc hmem hmag hU hfit')
    with s ⟨sFixed, sm, si, ss, sf, sh, sw⟩
  wram_exec [si, sFixed.one]
  wram_simp [sm, ss]
  refine ⟨sFixed.of_frame fun j hj => ?_, sf, sh, sw⟩
  have hne : j ≠ Reg.index := fun he => by
    subst j; norm_num [Reg.index, Reg.one, Reg.zero] at hj
  wram_simp [hne]

/-- Zero answers and an already successful flag incur no verifier call. In particular the
actual scan counter and all returned witness coordinates are preserved. -/
theorem exec_step_skip {W n first length out queries count i : ℕ} (x : Data 400)
    (hx : Fixed n first length out queries count x) (hi : x.regs Reg.index = i)
    (hskip : x.regs Reg.found ≠ 0 ∨ x.mem (out + i) = 0)
    (hfit : Fits W (out + i + 2)) :
    ∃ y, ExecWithin W step x y 6 ∧ Fixed n first length out queries count y ∧
      y.mem = x.mem ∧ y.regs Reg.index = i + 1 ∧
      ∀ j : Fin 400, j ≠ Reg.index → j ≠ Reg.address → j ≠ Reg.answer →
        y.regs j = x.regs j := by
  refine WP.exists_execWithin ?_
  unfold step
  by_cases hf : x.regs Reg.found = 0
  · have hz : x.mem (out + i) = 0 := hskip.resolve_left (not_not_intro hf)
    wram_exec [hf, hz, hi, hx.output, hx.zero, hx.one]
    refine ⟨hx.of_frame fun j hj => ?_, rfl, by wram_simp,
      fun j hj ha hb => by wram_simp [hj, ha, hb]⟩
    have hindex : j ≠ Reg.index := fun he => by
      subst j; norm_num [Reg.index, Reg.one, Reg.zero] at hj
    have haddr : j ≠ Reg.address := fun he => by
      subst j; norm_num [Reg.address, Reg.one, Reg.zero] at hj
    have hans : j ≠ Reg.answer := fun he => by
      subst j; norm_num [Reg.answer, Reg.one, Reg.zero] at hj
    wram_simp [hindex, haddr, hans]
  · wram_exec [hf, hi, hx.zero, hx.one]
    refine ⟨hx.of_frame fun j hj => ?_, rfl, by wram_simp,
      fun j hj _ hb => by wram_simp [hj, hb]⟩
    have hindex : j ≠ Reg.index := fun he => by
      subst j; norm_num [Reg.index, Reg.one, Reg.zero] at hj
    have hans : j ≠ Reg.answer := fun he => by
      subst j; norm_num [Reg.answer, Reg.one, Reg.zero] at hj
    wram_simp [hindex, hans]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
