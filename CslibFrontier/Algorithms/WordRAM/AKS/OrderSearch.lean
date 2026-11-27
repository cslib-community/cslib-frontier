/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.NatGcd
import Mathlib.Tactic.Linarith

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# The search for `r` in the AKS algorithm on the word RAM

Step 2 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] finds the least `r` such
that the multiplicative order of `n` modulo `r` exceeds a bound `L`. As in the proof of their
Theorem 5.1, the program tries `r = 2, 3, …` in turn. It accepts `r` when `gcd(n, r) = 1` and
`n^k mod r ≠ 1` for every `1 ≤ k ≤ L`; for `r ≥ 2` this is the order condition
(`Cslib.AKS.lt_orderOf_iff`). The powers are computed by one multiplication modulo `r` each, and
the gcd by Euclid's algorithm (`Cslib.Algorithms.WordRAM.NatGcd.program`). Given any `r₀ ≥ 2`
satisfying the condition, the search stops at some `2 ≤ r ≤ r₀` satisfying it, within a number of
instructions polynomial in `r₀` and `L`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.OrderSearch.Good`: the condition tested for one `r`.
* `Cslib.Algorithms.WordRAM.AKS.OrderSearch.program`: the search.
* `Cslib.Algorithms.WordRAM.AKS.OrderSearch.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.OrderSearch.exec`: the search stops at an `r ≤ r₀` satisfying the
  condition, within `time L r₀` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.OrderSearch

open Cslib.WordRAM

/-- The condition tested for `r`: `n` is coprime to `r` and no `n^k` with `1 ≤ k ≤ L` is `1`
modulo `r`. -/
def Good (n L r : ℕ) : Prop := n.Coprime r ∧ ∀ k, 1 ≤ k → k ≤ L → n ^ k % r ≠ 1

/-- The number `n`, preserved. -/
abbrev n : Fin 13 := 0
/-- The bound `L` on the order, preserved. -/
abbrev L : Fin 13 := 1
/-- The candidate `r`, and the output. -/
abbrev r : Fin 13 := 2
/-- `1` once a candidate is accepted. -/
abbrev found : Fin 13 := 3
/-- Constant one. -/
abbrev one : Fin 13 := 4
/-- `n mod r`. -/
abbrev nr : Fin 13 := 5
/-- The power `n^k mod r`. -/
abbrev p : Fin 13 := 6
/-- The exponent `k`. -/
abbrev k : Fin 13 := 7
/-- `1` while no power `n^j` with `1 ≤ j ≤ k` is `1` modulo `r`. -/
abbrev ok : Fin 13 := 8
/-- First argument of the gcd, and its result. -/
abbrev ga : Fin 13 := 9
/-- Second argument of the gcd. -/
abbrev gb : Fin 13 := 10

/-- Euclid's algorithm runs on `ga`, `gb` and two scratch registers. -/
def gcdMap : Fin 4 → Fin 13 := ![ga, gb, 11, 12]

theorem gcdMap_injective : gcdMap.Injective := by decide

/-- One more power: `p := p · (n mod r) mod r`, and record whether it is `1`. -/
def powBody : Code .standard 13 := ram[
  p ← p * nr; p ← p % r; k ← k + one; if p = one then [ ok ← #0 ] else [ ok ← ok ] ]

/-- Test the powers `n^k mod r` for `1 ≤ k ≤ L`. -/
def powers : Code .standard 13 :=
  .seq (ram[ nr ← n % r; p ← one; k ← #0; ok ← #1 ]) (.loop (.lt k L) powBody)

/-- Accept `r` if `gcd(n, r) = 1` and no small power is `1`; otherwise try `r + 1`. -/
def accept : Code .standard 13 := ram[
  if ga = one then [ if ok = one then [ found ← #1 ] else [ r ← r + one ] ] else [ r ← r + one ] ]

/-- Test one candidate. -/
def body : Code .standard 13 :=
  .seq powers (.seq (ram[ ga ← n; gb ← r ]) (.seq (NatGcd.program.rename gcdMap) accept))

/-- Try `r = 2, 3, …` until one is accepted. -/
def program : Code .standard 13 :=
  .seq (ram[ one ← #1; r ← #2; found ← #0 ]) (.loop (.lt found one) body)

/-- The instruction bound of `program`. -/
def time (L r₀ : ℕ) : ℕ := (2 * r₀ + 1) * (8 * L + 5 * r₀ + 20) + 5

/-- The registers that the power loop preserves. -/
private theorem loop_preserves :
    ∀ j ∈ [n, L, r, found, one], (Code.loop (.lt k L) powBody).Preserves j := by decide

private theorem powers_exec {w : ℕ} (x : Data 13) {N L₀ R : ℕ} (hn : x.regs n = N)
    (hL : x.regs L = L₀) (hr : x.regs r = R) (h1 : x.regs one = 1) (hR : 2 ≤ R)
    (hfN : Fits w N) (hfR : Fits w (R * R)) (hfL : Fits w (L₀ + 1)) :
    ∃ y, ExecWithin w powers x y (8 * L₀ + 6) ∧ y.regs ok ≤ 1 ∧
      (y.regs ok = 1 ↔ ∀ j, 1 ≤ j → j ≤ L₀ → N ^ j % R ≠ 1) ∧
      ∀ j ∈ [n, L, r, found, one], y.regs j = x.regs j := by
  have hR0 : 0 < R := by omega
  let J (j : ℕ) (y : Data 13) : Prop := y.regs L = L₀ ∧ y.regs r = R ∧ y.regs one = 1 ∧
    y.regs nr = N % R ∧ y.regs p = N ^ j % R ∧ y.regs ok ≤ 1 ∧
    (y.regs ok = 1 ↔ ∀ b, 1 ≤ b → b ≤ j → N ^ b % R ≠ 1)
  have hstep (y : Data 13) (hy : J (y.regs k) y) (hlt : y.regs k < L₀) :
      ∃ z, ExecWithin w powBody y z 6 ∧ J (y.regs k + 1) z ∧ z.regs k = y.regs k + 1 := by
    obtain ⟨hyL, hyr, hy1, hynr, hyp, hyok, hyiff⟩ := hy
    have hPR : N ^ y.regs k % R < R := Nat.mod_lt _ hR0
    have hNR : N % R < R := Nat.mod_lt _ hR0
    have hmul : N ^ y.regs k % R * (N % R) < R * R := Nat.mul_lt_mul'' hPR hNR
    have hmod : N ^ y.regs k % R * (N % R) % R = N ^ (y.regs k + 1) % R := by
      rw [← Nat.mul_mod, pow_succ]
    have hmod_lt : N ^ (y.regs k + 1) % R < R := Nat.mod_lt _ hR0
    have hR_le : R ≤ R * R := Nat.le_mul_self R
    have hiff : (∀ j, 1 ≤ j → j ≤ y.regs k + 1 → N ^ j % R ≠ 1) ↔
        (∀ j, 1 ≤ j → j ≤ y.regs k → N ^ j % R ≠ 1) ∧ N ^ (y.regs k + 1) % R ≠ 1 := by
      constructor
      · intro h; exact ⟨fun j hj hjK => h j hj (by omega), h (y.regs k + 1) (by omega) le_rfl⟩
      · rintro ⟨h, hK1⟩ j hj hjK
        rcases Nat.lt_or_ge j (y.regs k + 1) with hlt' | hge
        · exact h j hj (by omega)
        · rw [show j = y.regs k + 1 by omega]; exact hK1
    unfold powBody
    wram_exec [hyp, hynr, hyr, hy1, hmod] <;>
      { wram_simp [J, hyL, hyr, hy1, hynr, hyok, hyiff, hiff]; simp [hc] }
  have hNR_le : N % R ≤ N := Nat.mod_le N R
  unfold powers
  wram_exec [hn, hr, h1]
  refine WP.name fun x₀ hx₀ => ?_
  have hk₀ : x₀.regs k = 0 := by subst hx₀; wram_simp
  have hx₀J : J (x₀.regs k) x₀ := by
    subst hx₀
    simp only [J]
    wram_simp [hL, hr, h1]
    refine ⟨?_, ?_⟩
    · rw [pow_zero, Nat.mod_eq_of_lt (by omega : 1 < R)]
    · simp; omega
  obtain ⟨y, hrun, ⟨_, _, _, _, _, hyok, hyiff⟩, _⟩ := ExecWithin.loop_count J
    (fun _ hy => hy.1) hstep (by omega) hx₀J
  refine WP.of_execWithin hrun ⟨by omega, hyok, hyiff, fun j hj => ?_⟩
  rw [hrun.regs_eq (loop_preserves j hj)]
  subst hx₀
  rcases List.mem_cons.mp hj with rfl | hj
  · wram_simp
  rcases List.mem_cons.mp hj with rfl | hj
  · wram_simp
  rcases List.mem_cons.mp hj with rfl | hj
  · wram_simp
  rcases List.mem_cons.mp hj with rfl | hj
  · wram_simp
  simp only [List.mem_singleton] at hj; subst hj
  wram_simp [h1]

/-- **The search for `r`.** If some `r₀ ≥ 2` satisfies `Good n L r₀`, and the word size holds
`n`, `r₀²` and `L + 1`, the search stops within `time L r₀` instructions at some `2 ≤ r ≤ r₀`
satisfying `Good n L r`, preserving `n` and `L`. -/
theorem exec {w : ℕ} (x : Data 13) {N L₀ r₀ : ℕ} (hn : x.regs n = N) (hL : x.regs L = L₀)
    (hr₀ : 2 ≤ r₀) (hgood : Good N L₀ r₀) (hfN : Fits w N) (hfR : Fits w (r₀ * r₀))
    (hfL : Fits w (L₀ + 1)) :
    ∃ y, ExecWithin w program x y (time L₀ r₀) ∧ 2 ≤ y.regs r ∧ y.regs r ≤ r₀ ∧
      Good N L₀ (y.regs r) ∧ y.regs n = N ∧ y.regs L = L₀ := by
  have hfr₁ : Fits w (r₀ + 1) := hfR.of_le (by nlinarith)
  let I (y : Data 13) : Prop := y.regs n = N ∧ y.regs L = L₀ ∧ y.regs one = 1 ∧ 2 ≤ y.regs r ∧
    y.regs r ≤ r₀ ∧ y.regs found ≤ 1 ∧ (y.regs found = 1 → Good N L₀ (y.regs r))
  have hstep (y : Data 13) (hy : I y) (hlt_f : (Cond.lt found one).Holds y) :
      ∃ z, ExecWithin w body y z (8 * L₀ + 5 * r₀ + 16) ∧ I z ∧
        2 * (r₀ - z.regs r) + (1 - z.regs found) < 2 * (r₀ - y.regs r) + (1 - y.regs found) := by
    obtain ⟨hyn, hyL, hy1, hr2, hrr₀, hyf, -⟩ := hy
    obtain ⟨R, hR⟩ : ∃ R, y.regs r = R := ⟨_, rfl⟩
    rw [hR] at hr2 hrr₀
    have hf0 : y.regs found = 0 := by simp only [Cond.holds_lt, hy1] at hlt_f; omega
    unfold body
    wram_exec
    wram_call (powers_exec (w := w) y hyn hyL hR hy1 hr2 hfN
      (hfR.of_le (Nat.mul_le_mul hrr₀ hrr₀)) hfL) with y₁ ⟨hok1, hokiff, hy₁⟩
    have hy₁n : y₁.regs n = N := (hy₁ n (by simp)).trans hyn
    have hy₁r : y₁.regs r = R := (hy₁ r (by simp)).trans hR
    wram_exec [hy₁n, hy₁r]
    refine WP.name fun y₂ hy₂ => ?_
    have hy₂a : y₂.regs ga = N := by subst hy₂; wram_simp
    have hy₂b : y₂.regs gb = R := by subst hy₂; wram_simp
    wram_call (NatGcd.exec (y₂.comap gcdMap)
      (by change Fits w (y₂.regs ga); exact hy₂a ▸ hfN)
      (by change Fits w (y₂.regs gb); exact hy₂b ▸ hfR.of_le (hrr₀.trans (Nat.le_mul_self r₀))))
      renamed gcdMap_injective with y₃ ⟨⟨hg, -⟩, hout₃⟩
    have hgcd : y₃.regs ga = Nat.gcd N R := by
      change y₃.regs ga = (y₂.regs ga).gcd (y₂.regs gb) at hg
      rwa [hy₂a, hy₂b] at hg
    have hkeep : ∀ j ∈ [n, L, r, found, one, ok], (∀ i, gcdMap i ≠ j) ∧ j ≠ ga ∧ j ≠ gb := by
      decide
    have hy₃ {j : Fin 13} (hj : j ∈ [n, L, r, found, one, ok]) : y₃.regs j = y₁.regs j := by
      obtain ⟨h1, h2, h3⟩ := hkeep j hj
      rw [hout₃ j h1]; subst hy₂; wram_simp [h2, h3]
    have hy₃n : y₃.regs n = N := (hy₃ (by simp)).trans hy₁n
    have hy₃L : y₃.regs L = L₀ := (hy₃ (by simp)).trans ((hy₁ L (by simp)).trans hyL)
    have hy₃r : y₃.regs r = R := (hy₃ (by simp)).trans hy₁r
    have hy₃f : y₃.regs found = 0 := (hy₃ (by simp)).trans ((hy₁ found (by simp)).trans hf0)
    have hy₃1 : y₃.regs one = 1 := (hy₃ (by simp)).trans ((hy₁ one (by simp)).trans hy1)
    have hy₃ok : y₃.regs ok = y₁.regs ok := hy₃ (by simp)
    have hgood' : Good N L₀ R ↔ Nat.gcd N R = 1 ∧ y₁.regs ok = 1 := by
      rw [hokiff]; rfl
    unfold accept
    by_cases hg1 : Nat.gcd N R = 1
    · by_cases ho1 : y₁.regs ok = 1
      · have hG : Good N L₀ R := hgood'.mpr ⟨hg1, ho1⟩
        wram_exec [hgcd, hg1, hy₃1, hy₃ok, ho1]
        rw [show gcdMap NatGcd.b = gb from rfl, hy₂b]
        wram_simp [I, hy₃n, hy₃L, hy₃1, hy₃r, hy₃f, hR, hf0, hr2, hrr₀, hG]
        exact ⟨by omega, id, by omega⟩
      · have hne : R ≠ r₀ := fun h => ho1 (hgood'.mp (h ▸ hgood)).2
        wram_exec [hgcd, hg1, hy₃1, hy₃ok, ho1, hy₃r]
        rw [show gcdMap NatGcd.b = gb from rfl, hy₂b]
        wram_simp [I, hy₃n, hy₃L, hy₃1, hy₃r, hy₃f, hR, hf0]
        exact ⟨by omega, ⟨by omega, by omega, nofun⟩, by omega⟩
    · have hne : R ≠ r₀ := fun h => hg1 (hgood'.mp (h ▸ hgood)).1
      wram_exec [hgcd, hg1, hy₃1, hy₃r]
      rw [show gcdMap NatGcd.b = gb from rfl, hy₂b]
      wram_simp [I, hy₃n, hy₃L, hy₃1, hy₃r, hy₃f, hR, hf0]
      exact ⟨by omega, ⟨by omega, by omega, nofun⟩, by omega⟩
  unfold program
  wram_exec
  refine WP.name fun x₀ hx₀ => ?_
  have hx₀r : x₀.regs r = 2 := by subst hx₀; wram_simp
  have hx₀f : x₀.regs found = 0 := by subst hx₀; wram_simp
  have hx₀I : I x₀ := by
    subst hx₀; simp only [I]; wram_simp [hn, hL, hr₀]; nofun
  obtain ⟨y, hrun, ⟨hyn, hyL, hy1, hr2, hrr₀, _, hgoody⟩, hc⟩ := ExecWithin.loop_invariant I
    (fun y => 2 * (r₀ - y.regs r) + (1 - y.regs found)) hstep hx₀I
  have hf1 : y.regs found = 1 := by simp only [Cond.holds_lt, hy1] at hc; omega
  refine WP.of_execWithin hrun ⟨?_, hr2, hrr₀, hgoody hf1, hyn, hyL⟩
  have hμ : 2 * (r₀ - x₀.regs r) + (1 - x₀.regs found) ≤ 2 * r₀ + 1 := by omega
  have := Nat.mul_le_mul hμ (le_refl (8 * L₀ + 5 * r₀ + 16 + 2))
  unfold time
  nlinarith

end Cslib.Algorithms.WordRAM.AKS.OrderSearch
