/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
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
  have hfitN : Fits w N := hfit.of_le (by nlinarith)
  have h2 : Fits w 2 := hfit.of_le (by nlinarith)
  have h1 : Fits w 1 := hfit.of_le (by nlinarith)
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
    have hgood : Good (b + 1) ↔ Good b ∨ a ^ b = N := by
      constructor
      · rintro ⟨c, hc2, hcb, hc⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hcb with hcb | rfl
        · exact Or.inl ⟨c, hc2, hcb, hc⟩
        · exact Or.inr hc
      · rintro (⟨c, hc2, hcb, hc⟩ | h)
        · exact ⟨c, hc2, by omega, hc⟩
        · exact ⟨b, hk2, by omega, h⟩
    unfold body
    wram_exec
    wram_call (NatNthRoot.exec (y.comap rootMap) (by change 1 ≤ y.regs k; omega)
      (by change Fits w (y.regs k); exact hb ▸ hbfit)
      (by change Fits w (y.regs n * y.regs n + 2 * y.regs n + 2); exact hyn ▸ hfit))
      renamed rootMap_injective with y₁ ⟨⟨hy₁lo, hy₁n, hy₁k, hy₁o, hy₁t, hy₁m⟩, hout₁⟩
    have hy₁lo' : y₁.regs lo = a := by
      change y₁.regs lo = Nat.nthRoot (y.regs k) (y.regs n) at hy₁lo
      rwa [hb, hyn] at hy₁lo
    have hy₁n' : y₁.regs n = N := (show y₁.regs n = y.regs n from hy₁n).trans hyn
    have hy₁k' : y₁.regs k = b := (show y₁.regs k = y.regs k from hy₁k).trans hb
    wram_exec
    wram_call (NatNthRoot.CapPow.exec (y₁.comap capMap)
      (by change 1 ≤ y₁.regs lo; exact hy₁lo' ▸ ha1) h1
      (by change Fits w (y₁.regs k); exact hy₁k' ▸ hbfit)
      (by change Fits w (y₁.regs n * y₁.regs lo); rw [hy₁n', hy₁lo']
          exact hfit.of_le (by nlinarith)))
      renamed capMap_injective with y₂ ⟨⟨-, hpeq, -, hy₂k, hy₂n, hy₂o, hy₂m⟩, hout₂⟩
    have hy₂p : y₂.regs p = a ^ b := by
      change y₁.regs lo ^ y₁.regs k ≤ y₁.regs n → y₂.regs p = y₁.regs lo ^ y₁.regs k at hpeq
      rw [hy₁lo', hy₁k', hy₁n'] at hpeq
      exact hpeq hale
    have hy₂n' : y₂.regs n = N := (show y₂.regs n = y₁.regs n from hy₂n).trans hy₁n'
    have hy₂k' : y₂.regs k = b := (show y₂.regs k = y₁.regs k from hy₂k).trans hy₁k'
    have hy₂o' : y₂.regs one = 1 := hy₂o
    have hy₂t : y₂.regs two = 2 := (hout₂ two (by decide)).trans hy₁t
    have hy₂l : y₂.regs lim = L + 1 :=
      (hout₂ lim (by decide)).trans ((hout₁ lim (by decide)).trans hyl)
    have hy₂f : y₂.regs flag = if Good b then 1 else 0 :=
      (hout₂ flag (by decide)).trans ((hout₁ flag (by decide)).trans hyf)
    have hy₂m' : y₂.mem = x.mem := hy₂m.trans (hy₁m.trans hym)
    have hclog_le : Nat.clog 2 (N + 1) * (6 * b + 13) ≤ Nat.clog 2 (N + 1) * (6 * L + 13) :=
      Nat.mul_le_mul_left _ (by omega)
    wram_exec [hy₂p, hy₂n', hy₂o', hy₂k'] <;>
      { wram_simp [P, hT₀, hy₂n', hy₂o', hy₂t, hy₂l, hy₂f, hy₂m', hb, hgood]
        rw [show rootMap NatNthRoot.n = n from rfl, show rootMap NatNthRoot.k = k from rfl,
          show capMap NatNthRoot.CapPow.k = k from rfl, hyn, hb, hy₁k']
        simp [hc]; omega }
  unfold program
  wram_exec [hN]
  refine WP.name fun x₁ hx₁ => ?_
  have hx₁a : x₁.regs larg = N := by subst hx₁; wram_simp
  wram_call (NatLog.exec (x₁.comap logMap) h2
    (by change Fits w (x₁.regs larg); exact hx₁a ▸ hfitN)
    (by change Fits w (Nat.log 2 (x₁.regs larg) + 1); rw [hx₁a, hL]
        exact hfitN.of_le (by omega)))
    renamed logMap_injective with y₁ ⟨⟨hy₁r, hy₁m, hy₁o, hy₁t⟩, hout₁⟩
  have hy₁r' : y₁.regs lres = L := by
    change y₁.regs lres = Nat.log 2 (x₁.regs larg) at hy₁r
    rwa [hx₁a, hL] at hy₁r
  have hy₁o' : y₁.regs one = 1 := hy₁o
  have hy₁t' : y₁.regs two = 2 := hy₁t
  have hy₁n : y₁.regs n = N := (hout₁ n (by decide)).trans (by subst hx₁; wram_simp [hN])
  have hy₁m' : y₁.mem = x.mem := hy₁m.trans (by subst hx₁; rfl)
  wram_exec [hy₁r', hy₁o']
  refine WP.name fun x₂ hx₂ => ?_
  have hk₂ : x₂.regs k = 2 := by subst hx₂; wram_simp
  have hx₂P : P (x₂.regs k) x₂ := by
    have hgood2 : ¬Good 2 := fun ⟨c, hc2, hc, _⟩ => by omega
    subst hx₂
    simp only [P]
    wram_simp [hy₁n, hy₁o', hy₁t', hy₁m', hgood2]
  obtain ⟨y, hrun₃, ⟨hyn, _, _, _, _, hyf, hym⟩, _⟩ := ExecWithin.loop_count P
    (fun _ ⟨_, _, _, hlim, _⟩ => hlim) hbody (by omega) hx₂P
  refine WP.of_execWithin hrun₃ ⟨?_, ?_, hyn, hym⟩
  · have hx₂k : L + 1 - x₂.regs k ≤ L + 1 := by omega
    have := Nat.mul_le_mul_right (T₀ + 2) hx₂k
    rw [show logMap NatLog.arg = larg from rfl, hx₁a, hL]
    simp only [time, hL, hT₀] at this ⊢
    nlinarith
  · have hiff : Good (L + 1) ↔ Cslib.AKS.IsPerfectPower N := by
      rw [Cslib.AKS.isPerfectPower_iff_nthRoot hn]
      exact ⟨fun ⟨c, hc2, hck, hc⟩ => ⟨c, by omega, hc2, hc⟩,
        fun ⟨c, hcL, hc2, hc⟩ => ⟨c, hc2, by omega, hc⟩⟩
    rw [hyf]
    exact if_congr hiff rfl rfl

end Cslib.Algorithms.WordRAM.AKS.PerfectPower
