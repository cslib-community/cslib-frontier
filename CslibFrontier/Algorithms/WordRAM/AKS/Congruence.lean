/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
public import CslibFrontier.Algorithms.WordRAM.AKS.PolyArray
public import CslibFrontier.Algorithms.WordRAM.AKS.PolyPow

/-!
# The AKS congruence for one `a` on the word RAM

Step 5 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] tests
`(X + a)^n ≡ X^n + a (mod X^r - 1, n)`. The program writes the coefficients of `X + a` into a base
block `B` and those of `1` into a result block `R`, raises by repeated squaring
(`Cslib.Algorithms.WordRAM.AKS.PolyPow.program`) so that `R` holds `(X + a)^n`, writes the
coefficients of `X^n + a` into the scratch block `T`, and compares `R` with `T`. Both blocks are
reduced, so they agree exactly when the classes agree (`Cslib.AKS.toQuot_eq_toQuot_iff`), which is
the congruence (`Cslib.AKS.congruence_iff_toQuot`).

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.Congruence.program`: the congruence test.
* `Cslib.Algorithms.WordRAM.AKS.Congruence.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.Congruence.exec`: the flag is `1` exactly when
  `Cslib.AKS.Congruence n r a` holds, within `time r n` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.Congruence

open Cslib.WordRAM Cslib.AKS Polynomial

/-- Base address of the result block. -/
abbrev R : Fin 25 := 0
/-- Base address of the base block. -/
abbrev B : Fin 25 := 1
/-- Base address of the scratch block. -/
abbrev T : Fin 25 := 2
/-- The number `r` of coefficients. -/
abbrev rr : Fin 25 := 3
/-- The modulus `n`, which is also the exponent. -/
abbrev nn : Fin 25 := 4
/-- The exponent of the power. -/
abbrev e : Fin 25 := 5
/-- Block argument of the subroutines. -/
abbrev pa : Fin 25 := 9
/-- Second block argument of the comparison. -/
abbrev pb : Fin 25 := 10
/-- Constant one. -/
abbrev one : Fin 25 := 19
/-- The tested value `a`, preserved. -/
abbrev av : Fin 25 := 21
/-- The exponent residue for `Fill`. -/
abbrev er : Fin 25 := 22
/-- The constant term for `Fill`. -/
abbrev aa : Fin 25 := 23
/-- The answer: `1` when the congruence holds. -/
abbrev flag : Fin 25 := 24

/-- The power runs on the first `21` registers. -/
def powMap : Fin 21 → Fin 25 := Fin.castLE (by norm_num)

/-- `Fill` writes the block at `pa`, with scratch shared with the power. -/
def fillMap : Fin 10 → Fin 25 := ![pa, rr, nn, er, aa, 12, 15, 16, one, 20]

/-- `Compare` compares the blocks at `pa` and `pb`. -/
def cmpMap : Fin 9 → Fin 25 := ![pa, pb, rr, 12, 15, 16, 17, flag, one]

theorem powMap_injective : powMap.Injective := Fin.castLE_injective _
theorem fillMap_injective : fillMap.Injective := by decide
theorem cmpMap_injective : cmpMap.Injective := by decide

@[local wram_simps] private theorem map_regs :
    fillMap Fill.base = pa ∧ fillMap Fill.rr = rr ∧ fillMap Fill.nn = nn ∧
    fillMap Fill.er = er ∧ fillMap Fill.aa = aa ∧ fillMap Fill.one = one ∧
    powMap PolyPow.R = R ∧ powMap PolyPow.B = B ∧ powMap PolyPow.T = T ∧
    powMap PolyPow.rr = rr ∧ powMap PolyPow.nn = nn ∧ powMap PolyPow.e = e ∧
    cmpMap Compare.p = pa ∧ cmpMap Compare.q = pb ∧ cmpMap Compare.rr = rr ∧
    cmpMap Compare.flag = flag ∧ cmpMap Compare.one = one := by decide

/-- Write `X^e + a` into the block at `pa`. -/
def fill : Code .standard 25 := Fill.program.rename fillMap

/-- Raise `R` by `B` to the power in `e`. -/
def pow : Code .standard 25 := PolyPow.program.rename powMap

/-- Compare the blocks at `pa` and `pb`. -/
def cmp : Code .standard 25 := Compare.program.rename cmpMap

/-- Write `X + a` into `B` and `1` into `R`, raise to the power `n`, write `X^n + a` into `T`, and
compare `R` with `T`. -/
def program : Code .standard 25 :=
  .seq (ram[ one ← #1; er ← one % rr; aa ← av; pa ← B ]) (.seq fill
    (.seq (ram[ er ← #0; aa ← #0; pa ← R ]) (.seq fill
    (.seq (ram[ e ← nn ]) (.seq pow
    (.seq (ram[ er ← nn % rr; aa ← av; pa ← T ]) (.seq fill
    (.seq (ram[ pa ← R; pb ← T ]) cmp))))))))

/-- The instruction bound of `program`. -/
def time (r n : ℕ) : ℕ := PolyPow.time r n + 26 * r + 57

/-- The registers that every subroutine call preserves. -/
def Keep (j : Fin 25) : Prop := j = R ∨ j = B ∨ j = T ∨ j = rr ∨ j = nn ∨ j = av

instance : DecidablePred Keep := fun _ => by unfold Keep; infer_instance

/-- The class of `1`, written as `X^0 + 0`. -/
private theorem toQuot_one {n r : ℕ} (hr : 0 < r) : toQuot n r (powAddCoeff n r 0 0) = 1 := by
  rw [toQuot_powAddCoeff hr, pow_zero, Nat.cast_zero, C_0, add_zero, map_one]

/-- **The AKS congruence for one `a`.** For `r ≥ 1` and `n ≥ 1`, with the result, base and scratch
blocks `[a, a + r)`, `[b, b + r)` and `[t, t + r)` pairwise disjoint, and the word size holding the
block ends, `2 r`, `n² + n` and the tested value `A`, the program leaves `1` in `flag` if
`(X + A)^n ≡ X^n + A (mod X^r - 1, n)` and `0` otherwise, within `time r n` instructions. -/
theorem exec {w : ℕ} (x : Data 25) {a b t r n A : ℕ} (ha : x.regs R = a) (hb : x.regs B = b)
    (ht : x.regs T = t) (hr : x.regs rr = r) (hn : x.regs nn = n) (hA : x.regs av = A)
    (hr0 : 0 < r) (hn0 : 0 < n) (hab : a + r ≤ b ∨ b + r ≤ a) (hta : t + r ≤ a ∨ a + r ≤ t)
    (htb : t + r ≤ b ∨ b + r ≤ t) (hfa : Fits w (a + r)) (hfb : Fits w (b + r))
    (hft : Fits w (t + r)) (hf2 : Fits w (2 * r)) (hfn : Fits w (n * n + n)) (hfA : Fits w A) :
    ∃ y, ExecWithin w program x y (time r n) ∧ y.regs flag ≤ 1 ∧
      (y.regs flag = 1 ↔ Congruence n r A) ∧
      ∀ j, Keep j → y.regs j = x.regs j := by
  have h1 : Fits w 1 := hfn.of_le (by nlinarith)
  have hfn1 : Fits w (n + 1) := hfn.of_le (by nlinarith)
  have hfnn : Fits w n := hfn.of_le (by nlinarith)
  have hmod1 : 1 % r ≤ 1 := Nat.mod_le 1 r
  have hmodn : n % r ≤ n := Nat.mod_le n r
  unfold program fill pow cmp
  wram_exec [hr, hA, hb]
  wram_call (Fill.exec (w := w) (b := b) (r := r) (n := n) (e := 1) (a := A)) renamed
    [hn, hr0, hn0, hfb, hfA, hfn1] with y₁ ⟨⟨hB₁, -, -, hy₁r, hy₁n⟩, hout₁⟩
  wram_simp at hy₁r hy₁n
  have hy₁R : y₁.regs R = a := by regs_frame
  wram_exec [hy₁R]
  wram_call (Fill.exec (w := w) (b := a) (r := r) (n := n) (e := 0) (a := 0)) renamed
    [hy₁r, hy₁n, Nat.zero_mod, hr0, hn0, hfa, fits_zero w, hfn1]
    with y₂ ⟨⟨hR₂, hfr₂, -, hy₂r, hy₂n⟩, hout₂⟩
  wram_simp at hy₂r hy₂n hfr₂
  have hB₂ (k : ℕ) (hk : k < r) : y₂.mem (b + k) = powAddCoeff n r 1 A k := by
    have : ¬(a ≤ b + k ∧ b + k < a + r) := by rcases hab with h | h <;> omega
    mem_frame
  wram_exec [hy₂n]
  wram_call (PolyPow.exec (w := w) (a := a) (b := b) (t := t) (r := r) (n := n)) renamed
    powMap_injective [ha, hb, ht, hy₂r, hy₂n, hn0, hab, hta, htb, hfa, hfb, hft, hf2, hfn, hfnn]
    with y₃ ⟨⟨hq₃, hred₃, hy₃R, hy₃B, hy₃T, hy₃r, hy₃n⟩, hout₃⟩
  · wram_simp at hy₃R hy₃B hy₃T hy₃r hy₃n hq₃
    have hy₃A : y₃.regs av = A := by regs_frame
    wram_exec [hy₃n, hy₃r, hy₃A, hy₃T]
    wram_call (Fill.exec (w := w) (b := t) (r := r) (n := n) (e := n) (a := A)) renamed
      [hy₃r, hy₃n, hr0, hn0, hft, hfA, hfn1] with y₄ ⟨⟨hT₄, hfr₄, -, hy₄r, hy₄n⟩, hout₄⟩
    wram_simp at hy₄r hy₄n hfr₄
    have hR₄ (k : ℕ) (hk : k < r) : y₄.mem (a + k) = y₃.mem (a + k) := by
      have : ¬(t ≤ a + k ∧ a + k < t + r) := by rcases hta with h | h <;> omega
      mem_frame
    have hy₄R : y₄.regs R = a := by regs_frame
    have hy₄T : y₄.regs T = t := by regs_frame
    wram_exec [hy₄R, hy₄T]
    wram_call (Compare.exec (w := w) (a := a) (b := t) (r := r)) renamed
      [hy₄r, hfa, hft, h1] with y₅ ⟨⟨hle, hiff, -⟩, hout₅⟩
    wram_simp at hle hiff ⊢
    refine ⟨by unfold time; omega, hle, ?_, ?_⟩
    · rw [hiff, congruence_iff_toQuot hr0, ← toQuot_eq_toQuot_iff hn0 hr0
          (fun k hk => (hR₄ k hk).trans_lt (hred₃ k hk))
          (fun k hk => (hT₄ k hk).trans_lt (powAddCoeff_lt hn0 _ _ _)),
        toQuot_congr hR₄, hq₃, toQuot_congr hT₄, toQuot_congr hR₂, toQuot_congr hB₂,
        toQuot_one hr0, one_mul]
    · rintro j (rfl | rfl | rfl | rfl | rfl | rfl) <;> regs_frame
  · exact fun i hi => (hR₂ i hi).trans_lt (powAddCoeff_lt hn0 _ _ _)
  · exact fun i hi => (hB₂ i hi).trans_lt (powAddCoeff_lt hn0 _ _ _)

end Cslib.Algorithms.WordRAM.AKS.Congruence
