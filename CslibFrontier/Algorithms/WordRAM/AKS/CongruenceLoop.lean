/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.AKS.Congruence

import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Step 5 of the AKS algorithm on the word RAM

Step 5 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] tests the congruence
`(X + a)^n ≡ X^n + a (mod X^r - 1, n)` for `a = 1, …, A`. The program runs the test for one `a`
(`Cslib.Algorithms.WordRAM.AKS.Congruence.program`) for each `a` in turn and clears a flag when
one fails.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.CongruenceLoop.program`: the loop.
* `Cslib.Algorithms.WordRAM.AKS.CongruenceLoop.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.CongruenceLoop.exec`: the flag is `1` exactly when the congruence
  holds for every `1 ≤ a ≤ A`, within `time r n A` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.CongruenceLoop

open Cslib.WordRAM Cslib.AKS

/-- Base address of the result block. -/
abbrev R : Fin 29 := 0
/-- Base address of the base block. -/
abbrev B : Fin 29 := 1
/-- Base address of the scratch block. -/
abbrev T : Fin 29 := 2
/-- The number `r` of coefficients. -/
abbrev rr : Fin 29 := 3
/-- The modulus `n`. -/
abbrev nn : Fin 29 := 4
/-- The tested value `a`, which is also the loop index. -/
abbrev av : Fin 29 := 21
/-- The answer of one test. -/
abbrev flag : Fin 29 := 24
/-- The last tested value `A`, preserved. -/
abbrev A : Fin 29 := 25
/-- The loop end `A + 1`. -/
abbrev lim : Fin 29 := 26
/-- `1` while every test so far has passed. -/
abbrev ok : Fin 29 := 27
/-- Constant one. -/
abbrev c1 : Fin 29 := 28

/-- The test for one `a` runs on the first `25` registers. -/
def congMap : Fin 25 → Fin 29 := Fin.castLE (by norm_num)

theorem congMap_injective : congMap.Injective := Fin.castLE_injective _

/-- The test for one `a`. -/
def cong : Code .standard 29 := Congruence.program.rename congMap

/-- Test `a`, record a failure, and advance `a`. -/
def body : Code .standard 29 :=
  .seq cong (ram[ if flag = c1 then [ ok ← ok ] else [ ok ← #0 ]; av ← av + c1 ])

/-- Test `a = 1, …, A`. -/
def program : Code .standard 29 :=
  .seq (ram[ c1 ← #1; lim ← A + c1; av ← c1; ok ← #1 ]) (.loop (.lt av lim) body)

/-- The instruction bound of `program`. -/
def time (r n A : ℕ) : ℕ := A * (Congruence.time r n + 6) + 6

/-- **Step 5.** For `r ≥ 1` and `n ≥ 1`, with the three blocks pairwise disjoint and the word size
holding the block ends, `2 r`, `n² + n` and `A + 1`, the program leaves `1` in `ok` exactly when
`(X + a)^n ≡ X^n + a (mod X^r - 1, n)` for every `1 ≤ a ≤ A`, within `time r n A` instructions. -/
theorem exec {w : ℕ} (x : Data 29) {a b t r n A₀ : ℕ} (ha : x.regs R = a) (hb : x.regs B = b)
    (ht : x.regs T = t) (hr : x.regs rr = r) (hn : x.regs nn = n) (hA : x.regs A = A₀)
    (hr0 : 0 < r) (hn0 : 0 < n) (hab : a + r ≤ b ∨ b + r ≤ a) (hta : t + r ≤ a ∨ a + r ≤ t)
    (htb : t + r ≤ b ∨ b + r ≤ t) (hfa : Fits w (a + r)) (hfb : Fits w (b + r))
    (hft : Fits w (t + r)) (hf2 : Fits w (2 * r)) (hfn : Fits w (n * n + n))
    (hfA : Fits w (A₀ + 1)) :
    ∃ y, ExecWithin w program x y (time r n A₀) ∧ y.regs ok ≤ 1 ∧
      (y.regs ok = 1 ↔ ∀ v, 1 ≤ v → v ≤ A₀ → Congruence n r v) ∧
      y.regs R = a ∧ y.regs B = b ∧ y.regs T = t ∧ y.regs rr = r ∧ y.regs nn = n := by
  classical
  let P (j : ℕ) (y : Data 29) : Prop := y.regs R = a ∧ y.regs B = b ∧ y.regs T = t ∧ y.regs rr = r ∧
    y.regs nn = n ∧ y.regs lim = A₀ + 1 ∧ y.regs c1 = 1 ∧ 1 ≤ j ∧ y.regs ok ≤ 1 ∧
    (y.regs ok = 1 ↔ ∀ v, 1 ≤ v → v < j → Congruence n r v)
  have hstep (y : Data 29) (hy : P (y.regs av) y) (hlt : y.regs av < A₀ + 1) :
      ∃ z, ExecWithin w body y z (Congruence.time r n + 4) ∧
        P (y.regs av + 1) z ∧ z.regs av = y.regs av + 1 := by
    obtain ⟨hyR, hyB, hyT, hyr, hyn, hyl, hy1, hv1, hyok, hyiff⟩ := hy
    obtain ⟨V, hV⟩ : ∃ V, y.regs av = V := ⟨_, rfl⟩
    have hVA : V ≤ A₀ := by rw [hV] at hlt; omega
    rw [hV] at hv1 hyiff
    unfold body cong
    wram_exec
    wram_call (Congruence.exec (y.comap congMap) hyR hyB hyT hyr hyn hV hr0 hn0 hab hta htb
      hfa hfb hft hf2 hfn (hfA.of_le (by omega)))
      renamed congMap_injective with y₁ ⟨⟨hle, hiff, hkeep⟩, hout₁⟩
    have hy₁R : y₁.regs R = a := (hkeep Congruence.R (by simp [Congruence.Keep])).trans hyR
    have hy₁B : y₁.regs B = b := (hkeep Congruence.B (by simp [Congruence.Keep])).trans hyB
    have hy₁T : y₁.regs T = t := (hkeep Congruence.T (by simp [Congruence.Keep])).trans hyT
    have hy₁r : y₁.regs rr = r := (hkeep Congruence.rr (by simp [Congruence.Keep])).trans hyr
    have hy₁n : y₁.regs nn = n := (hkeep Congruence.nn (by simp [Congruence.Keep])).trans hyn
    have hy₁v : y₁.regs av = V := (hkeep Congruence.av (by simp [Congruence.Keep])).trans hV
    have hy₁l : y₁.regs lim = A₀ + 1 := (hout₁ lim (by decide)).trans hyl
    have hy₁ok : y₁.regs ok = y.regs ok := hout₁ ok (by decide)
    have hy₁1 : y₁.regs c1 = 1 := (hout₁ c1 (by decide)).trans hy1
    have hall_iff : (∀ v, 1 ≤ v → v < V + 1 → Congruence n r v) ↔
        (∀ v, 1 ≤ v → v < V → Congruence n r v) ∧ Congruence n r V :=
      ⟨fun h => ⟨fun v hv1' hv => h v hv1' (by omega), h V hv1 (by omega)⟩,
       fun ⟨h, hC⟩ v hv1' hv => (Nat.lt_succ_iff_lt_or_eq.mp hv).elim (h v hv1') (· ▸ hC)⟩
    by_cases hC : Congruence n r V
    · have hf1 : y₁.regs flag = 1 := hiff.mpr hC
      wram_exec [hf1, hy₁1, hy₁ok, hy₁v]
      wram_simp [P, hy₁R, hy₁B, hy₁T, hy₁r, hy₁n, hy₁l, hy₁1, hV, hyok, hyiff, hall_iff]
      simp [hC]
    · have hf1 : ¬ y₁.regs flag = 1 := fun h => hC (hiff.mp h)
      wram_exec [hf1, hy₁1, hy₁v]
      wram_simp [P, hy₁R, hy₁B, hy₁T, hy₁r, hy₁n, hy₁l, hy₁1, hV, hall_iff]
      simp [hC]
  unfold program
  wram_exec [hA]
  refine WP.name fun x₀ hx₀ => ?_
  have hv₀ : x₀.regs av = 1 := by subst hx₀; wram_simp
  have hx₀P : P (x₀.regs av) x₀ := by
    subst hx₀
    simp only [P]
    wram_simp [ha, hb, ht, hr, hn]
    simp; omega
  obtain ⟨y, hrun, ⟨hyR, hyB, hyT, hyr, hyn, _, _, _, hyok, hyiff⟩, _⟩ :=
    ExecWithin.loop_count P (fun _ ⟨_, _, _, _, _, hlim, _⟩ => hlim) hstep
      (by omega) hx₀P
  refine WP.of_execWithin hrun ⟨?_, hyok, ?_, hyR, hyB, hyT, hyr, hyn⟩
  · rw [hv₀, Nat.add_sub_cancel, time]
  · simp only [hyiff, Nat.lt_succ_iff]

end Cslib.Algorithms.WordRAM.AKS.CongruenceLoop
