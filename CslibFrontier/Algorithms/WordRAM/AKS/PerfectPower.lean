/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
public import CslibFrontier.Algorithms.WordRAM.NatLog
public import CslibFrontier.Algorithms.WordRAM.NatNthRoot
public import CslibFrontier.Foundations.NumberTheory.AKS.PerfectPower

import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Perfect-power detection on the word RAM

Step 1 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] asks whether `n = a ^ b`
for some `b > 1`. For `n ≥ 2` such an `a` is at least `2`, so `b ≤ log₂ n`, and `n` is a `b`-th
power exactly when `Nat.nthRoot b n ^ b = n` (`Cslib.AKS.isPerfectPower_iff_nthRoot`). The program
computes `⌊log₂ n⌋`, and for each `b` from `2` to `⌊log₂ n⌋` takes the `b`-th root by binary search
(`Cslib.Algorithms.WordRAM.NatNthRoot.program`) and compares its capped `b`-th power with `n`.
Every intermediate value is at most `n² + 2n + 1`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.PerfectPower.program`: the perfect-power test.
* `Cslib.Algorithms.WordRAM.AKS.PerfectPower.time`: its instruction bound, `O(log³ n)`.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.PerfectPower.exec`: the program decides `Cslib.AKS.IsPerfectPower`
  for `n ≥ 2` within `time n` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.PerfectPower

open Cslib.WordRAM

/-- The candidate `n`, preserved. -/
abbrev n : Fin 14 := 0
/-- The current exponent `b`. -/
abbrev k : Fin 14 := 1
/-- The root found by the search. -/
abbrev lo : Fin 14 := 2
/-- Upper end of the search interval. -/
abbrev hi : Fin 14 := 3
/-- Probe of the search. -/
abbrev mid : Fin 14 := 4
/-- Capped power. -/
abbrev p : Fin 14 := 5
/-- Counter of the capped power. -/
abbrev i : Fin 14 := 6
/-- Constant one. -/
abbrev one : Fin 14 := 7
/-- Constant two. -/
abbrev two : Fin 14 := 8
/-- Loop test of the search. -/
abbrev t : Fin 14 := 9
/-- `⌊log₂ n⌋ + 1`, the end of the exponent loop. -/
abbrev lim : Fin 14 := 10
/-- The answer: `1` for a perfect power. -/
abbrev flag : Fin 14 := 11
/-- Argument of the logarithm, consumed. -/
abbrev larg : Fin 14 := 12
/-- `⌊log₂ n⌋`. -/
abbrev lres : Fin 14 := 13

/-- The root search runs on the first ten registers. -/
def rootMap : Fin 10 → Fin 14 := Fin.castLE (by norm_num)

/-- The final capped power raises the root `lo` to the exponent `k`. -/
def capMap : Fin 6 → Fin 14 := ![lo, k, n, p, i, one]

/-- The logarithm runs on `larg`, `lres` and the shared constants. -/
def logMap : Fin 4 → Fin 14 := ![larg, lres, one, two]

theorem rootMap_injective : rootMap.Injective := Fin.castLE_injective _
theorem capMap_injective : capMap.Injective := by decide
theorem logMap_injective : logMap.Injective := by decide

@[local wram_simps] private theorem map_regs :
    rootMap NatNthRoot.n = n ∧ rootMap NatNthRoot.k = k ∧ rootMap NatNthRoot.lo = lo ∧
    rootMap NatNthRoot.one = one ∧ rootMap NatNthRoot.two = two ∧
    capMap NatNthRoot.CapPow.m = lo ∧ capMap NatNthRoot.CapPow.k = k ∧
    capMap NatNthRoot.CapPow.n = n ∧ capMap NatNthRoot.CapPow.p = p ∧
    capMap NatNthRoot.CapPow.one = one ∧
    logMap NatLog.arg = larg ∧ logMap NatLog.result = lres ∧
    logMap NatLog.one = one ∧ logMap NatLog.two = two := by decide

/-- Test one exponent: take the root, raise it back, and record equality with `n`. -/
def body : Code .standard 14 :=
  .seq (NatNthRoot.program.rename rootMap) (.seq (NatNthRoot.CapPow.program.rename capMap)
    (ram[ if p = n then [ flag ← one ] else [ flag ← flag ]; k ← k + one ]))

/-- Compute `⌊log₂ n⌋`, then test every exponent `2 ≤ b ≤ ⌊log₂ n⌋`. -/
def program : Code .standard 14 :=
  .seq (ram[ larg ← n ]) (.seq (NatLog.program.rename logMap)
    (.seq (ram[ lim ← lres + one; flag ← #0; k ← #2 ]) (.loop (.lt k lim) body)))

/-- The instruction bound of `program`, which is `O(log³ n)`. -/
def time (n : ℕ) : ℕ :=
  (Nat.log 2 n + 1) * (Nat.clog 2 (n + 1) * (6 * Nat.log 2 n + 13) + 6 * Nat.log 2 n + 22) +
    4 * Nat.log 2 n + 11

/-- **The perfect-power test.** For `n ≥ 2` and a word size holding `n² + 2n + 2`, the program
leaves `1` in `flag` if `n` is a perfect power and `0` otherwise, within `time n` instructions,
preserving `n` and memory. -/
theorem exec {w : ℕ} (x : Data 14) (hn : 2 ≤ x.regs n)
    (hfit : Fits w (x.regs n * x.regs n + 2 * x.regs n + 2)) :
    ∃ y, ExecWithin w program x y (time (x.regs n)) ∧
      y.regs flag = (if Cslib.AKS.IsPerfectPower (x.regs n) then 1 else 0) ∧
      y.regs n = x.regs n ∧ y.mem = x.mem := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, x.regs n = N := ⟨_, rfl⟩
  rw [hN] at hn hfit ⊢
  obtain ⟨L, hL⟩ : ∃ L, Nat.log 2 N = L := ⟨_, rfl⟩
  have hLN : L < N := hL ▸ Nat.log_lt_self 2 (by omega)
  have hLpos : 1 ≤ L := hL ▸ Nat.le_log_of_pow_le one_lt_two (by omega)
  have hfitN : Fits w N := hfit.of_le (by omega)
  have h2 : Fits w 2 := hfit.of_le (by omega)
  have h1 : Fits w 1 := hfit.of_le (by omega)
  let Good (b : ℕ) : Prop := ∃ c, 2 ≤ c ∧ c < b ∧ Nat.nthRoot c N ^ c = N
  let P (j : ℕ) (y : Data 14) : Prop := y.regs n = N ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
    y.regs lim = L + 1 ∧ 2 ≤ j ∧
    y.regs flag = (if Good j then 1 else 0) ∧ y.mem = x.mem
  set T₀ := Nat.clog 2 (N + 1) * (6 * L + 13) + 6 * L + 18 with hT₀
  have hbody (y : Data 14) (hy : P (y.regs k) y) (hlt : y.regs k < L + 1) :
      ∃ z, ExecWithin w body y z T₀ ∧
        P (y.regs k + 1) z ∧ z.regs k = y.regs k + 1 := by
    obtain ⟨hyn, hyo, hyt, hyl, hk2, hyf, hym⟩ := hy
    obtain ⟨b, hb⟩ : ∃ b, y.regs k = b := ⟨_, rfl⟩
    have hkL' : b ≤ L := by rw [hb] at hlt; omega
    rw [hb] at hk2 hyf
    have hbfit : Fits w b := hfitN.of_le (by omega)
    set a := Nat.nthRoot b N
    have hb0 : b ≠ 0 := by omega
    have hale : a ^ b ≤ N := Nat.pow_nthRoot_le_iff.mpr (Or.inl hb0)
    have ha1 : 1 ≤ a := (Nat.le_nthRoot_iff hb0).mpr (by rw [one_pow]; omega)
    have haN : a ≤ N := (Nat.le_self_pow hb0 a).trans hale
    have hprod_le : N * a ≤ N * N + 2 * N + 2 :=
      (Nat.mul_le_mul_left N haN).trans (by omega)
    have hgood : Good (b + 1) ↔ Good b ∨ a ^ b = N := by
      constructor
      · rintro ⟨c, hc2, hcb, hc⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hcb with hcb | rfl
        · exact Or.inl ⟨c, hc2, hcb, hc⟩
        · exact Or.inr hc
      · rintro (⟨c, hc2, hcb, hc⟩ | h)
        · exact ⟨c, hc2, by omega, hc⟩
        · exact ⟨b, hk2, by omega, h⟩
    apply WP.exists_execWithin
    unfold body
    wram_call (NatNthRoot.exec (w := w)) renamed rootMap_injective
      [hb, hyn, show 1 ≤ b by omega, hbfit, hfit]
      with y₁ ⟨⟨hy₁lo, hy₁n, hy₁k, hy₁o, hy₁t, hy₁m⟩, hout₁⟩
    wram_simp [hb, hyn] at hy₁lo hy₁n hy₁k hy₁o hy₁t
    wram_call (NatNthRoot.CapPow.exec (w := w)) renamed
      [hy₁lo, hy₁k, hy₁n, ha1, h1, hbfit, hfit.of_le hprod_le]
      with y₂ ⟨⟨-, hpeq, -, hy₂k, hy₂n, hy₂o, hy₂m⟩, hout₂⟩
    wram_simp [hy₁lo, hy₁k, hy₁n] at hpeq hy₂k hy₂n hy₂o
    have hy₂p : y₂.regs p = a ^ b := hpeq hale
    have hy₂t : y₂.regs two = 2 := by regs_frame
    have hy₂l : y₂.regs lim = L + 1 := by regs_frame
    have hy₂f : y₂.regs flag = if Good b then 1 else 0 := by regs_frame
    have hy₂m' : y₂.mem = x.mem := by mem_frame
    have hclog_le : Nat.clog 2 (N + 1) * (6 * b + 13) ≤ Nat.clog 2 (N + 1) * (6 * L + 13) :=
      Nat.mul_le_mul_left _ (by omega)
    wram_exec [hy₂p, hy₂n, hy₂o, hy₂k] <;>
      { wram_simp [P, hT₀, hy₁k, hy₂n, hy₂o, hy₂t, hy₂l, hy₂f, hy₂m', hb, hyn, hgood]
        simp [hc]; omega }
  unfold program
  wram_exec [hN]
  wram_call (NatLog.exec (w := w)) renamed
    [hL, h2, hfitN, hfitN.of_le (by omega : L + 1 ≤ N)]
    with y₁ ⟨⟨hy₁r, hy₁m, hy₁o, hy₁t⟩, hout₁⟩
  wram_simp [hL] at hy₁r hy₁o hy₁t
  have hy₁n : y₁.regs n = N := by regs_frame
  have hy₁m' : y₁.mem = x.mem := by mem_frame
  wram_exec [hy₁r, hy₁o]
  wram_call (ExecWithin.loop_count P (fun _ ⟨_, _, _, hlim, _⟩ => hlim) hbody)
    with y ⟨⟨hyn, _, _, _, _, hyf, hym⟩, _⟩
  · wram_simp [hL]
    refine ⟨?_, ?_, hyn, hym⟩
    · have h1le := Nat.mul_le_mul_right (T₀ + 2) (show L + 1 - 2 ≤ L + 1 by omega)
      have h2le := Nat.mul_le_mul_left (L + 1)
        (show T₀ + 2 ≤ Nat.clog 2 (N + 1) * (6 * L + 13) + 6 * L + 22 by rw [hT₀]; omega)
      simp only [time, hL] at h2le ⊢
      omega
    · have hiff : Good (L + 1) ↔ Cslib.AKS.IsPerfectPower N := by
        rw [Cslib.AKS.isPerfectPower_iff_nthRoot hn]
        exact ⟨fun ⟨c, hc2, hck, hc⟩ => ⟨c, by omega, hc2, hc⟩,
          fun ⟨c, hcL, hc2, hc⟩ => ⟨c, hc2, by omega, hc⟩⟩
      rw [hyf]
      exact if_congr hiff rfl rfl
  · have hgood2 : ¬Good 2 := fun ⟨c, hc2, hc, _⟩ => by omega
    wram_simp [P, hy₁n, hy₁o, hy₁t, hy₁r, hy₁m', hgood2]

end Cslib.Algorithms.WordRAM.AKS.PerfectPower
