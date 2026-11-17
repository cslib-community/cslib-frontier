/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
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

private theorem fill_preserves : ∀ j, Keep j → fill.Preserves j := by decide
private theorem cmp_preserves : ∀ j, Keep j → cmp.Preserves j := by decide

private theorem fill_exec {w : ℕ} (x : Data 25) {bs r n e' A : ℕ} (hb : x.regs pa = bs)
    (hr : x.regs rr = r) (hn : x.regs nn = n) (her : x.regs er = e' % r) (ha : x.regs aa = A)
    (hr0 : 0 < r) (hn0 : 0 < n) (hfb : Fits w (bs + r)) (hfa : Fits w A) (hfn : Fits w (n + 1)) :
    ∃ y, ExecWithin w fill x y (5 * r + 13) ∧
      (∀ k < r, y.mem (bs + k) = powAddCoeff n r e' A k) ∧
      (∀ a', ¬(bs ≤ a' ∧ a' < bs + r) → y.mem a' = x.mem a') ∧
      (∀ j, Keep j → y.regs j = x.regs j) := by
  obtain ⟨y, hy, hblk, hframe, -⟩ := Fill.exec (x.comap fillMap) hb hr hn her ha hr0 hn0 hfb hfa hfn
  have hy' := hy.rename fillMap_injective
  exact ⟨_, hy', hblk, hframe, fun j hj => hy'.regs_eq (fill_preserves j hj)⟩

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
  unfold program
  wram_exec [hr, hA, hb]
  refine WP.name fun x₁ hx₁ => ?_
  have hx₁k (j : Fin 25) (hj : Keep j) : x₁.regs j = x.regs j := by
    subst hx₁; rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> wram_simp
  wram_call (fill_exec (w := w) x₁ (bs := b) (r := r) (n := n) (e' := 1) (A := A)
    (by subst hx₁; wram_simp) ((hx₁k rr (by simp [Keep])).trans hr)
    ((hx₁k nn (by simp [Keep])).trans hn) (by subst hx₁; wram_simp)
    (by subst hx₁; wram_simp) hr0 hn0 hfb hfA hfn1) with y₁ ⟨hB₁, -, hy₁⟩
  have hy₁' (j : Fin 25) (hj : Keep j) : y₁.regs j = x.regs j :=
    (hy₁ j hj).trans (hx₁k j hj)
  wram_exec [hy₁' R (by simp [Keep]), ha]
  refine WP.name fun x₂ hx₂ => ?_
  have hx₂k (j : Fin 25) (hj : Keep j) : x₂.regs j = x.regs j := by
    rw [← hy₁' j hj]; subst hx₂
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> wram_simp
  have hx₂m : x₂.mem = y₁.mem := by subst hx₂; rfl
  wram_call (fill_exec (w := w) x₂ (bs := a) (r := r) (n := n) (e' := 0) (A := 0)
    (by subst hx₂; wram_simp) ((hx₂k rr (by simp [Keep])).trans hr)
    ((hx₂k nn (by simp [Keep])).trans hn) (by subst hx₂; wram_simp [Nat.zero_mod])
    (by subst hx₂; wram_simp) hr0 hn0 hfa (fits_zero w) hfn1) with y₂ ⟨hR₂, hfr₂, hy₂⟩
  have hy₂' (j : Fin 25) (hj : Keep j) : y₂.regs j = x.regs j :=
    (hy₂ j hj).trans (hx₂k j hj)
  have hB₂ (k : ℕ) (hk : k < r) : y₂.mem (b + k) = powAddCoeff n r 1 A k :=
    (hfr₂ _ (by rcases hab with h | h <;> omega)).trans (hx₂m ▸ hB₁ k hk)
  wram_exec [hy₂' nn (by simp [Keep]), hn]
  refine WP.name fun x₃ hx₃ => ?_
  have hx₃k (j : Fin 25) (hj : Keep j) : x₃.regs j = x.regs j := by
    rw [← hy₂' j hj]; subst hx₃
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> wram_simp
  have hx₃e : x₃.regs e = n := by subst hx₃; wram_simp
  have hx₃m : x₃.mem = y₂.mem := by subst hx₃; rfl
  unfold pow
  wram_call (PolyPow.exec (x₃.comap powMap)
    ((hx₃k R (by simp [Keep])).trans ha) ((hx₃k B (by simp [Keep])).trans hb)
    ((hx₃k T (by simp [Keep])).trans ht) ((hx₃k rr (by simp [Keep])).trans hr)
    ((hx₃k nn (by simp [Keep])).trans hn) hn0 hab hta htb
    (fun i hi => by change x₃.mem (a + i) < n; rw [hx₃m, hR₂ i hi]; exact powAddCoeff_lt hn0 _ _ _)
    (fun i hi => by change x₃.mem (b + i) < n; rw [hx₃m, hB₂ i hi]; exact powAddCoeff_lt hn0 _ _ _)
    hfa hfb hft hf2 hfn (by change Fits w (x₃.regs e); exact hx₃e ▸ hfnn))
    renamed powMap_injective with y₃ ⟨⟨hq₃, hred₃, hy₃R, hy₃B, hy₃T, hy₃r, hy₃n⟩, hout₃⟩
  change toQuot n r (fun i => y₃.mem (a + i)) =
    toQuot n r (fun i => x₃.mem (a + i)) * toQuot n r (fun i => x₃.mem (b + i)) ^ x₃.regs e at hq₃
  rw [hx₃e, hx₃m] at hq₃
  have hy₃' (j : Fin 25) (hj : Keep j) : y₃.regs j = x.regs j := by
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (show y₃.regs R = a from hy₃R).trans ha.symm
    · exact (show y₃.regs B = b from hy₃B).trans hb.symm
    · exact (show y₃.regs T = t from hy₃T).trans ht.symm
    · exact (show y₃.regs rr = r from hy₃r).trans hr.symm
    · exact (show y₃.regs nn = n from hy₃n).trans hn.symm
    · exact (hout₃ av (by decide)).trans (hx₃k av (by simp [Keep]))
  wram_exec [hy₃' nn (by simp [Keep]), hn, hy₃' rr (by simp [Keep]), hr,
    hy₃' av (by simp [Keep]), hA, hy₃' T (by simp [Keep]), ht]
  refine WP.name fun x₄ hx₄ => ?_
  have hx₄k (j : Fin 25) (hj : Keep j) : x₄.regs j = x.regs j := by
    rw [← hy₃' j hj]; subst hx₄
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> wram_simp
  have hx₄m : x₄.mem = y₃.mem := by subst hx₄; rfl
  wram_call (fill_exec (w := w) x₄ (bs := t) (r := r) (n := n) (e' := n) (A := A)
    (by subst hx₄; wram_simp) ((hx₄k rr (by simp [Keep])).trans hr)
    ((hx₄k nn (by simp [Keep])).trans hn) (by subst hx₄; wram_simp)
    (by subst hx₄; wram_simp) hr0 hn0 hft hfA hfn1) with y₄ ⟨hT₄, hfr₄, hy₄⟩
  have hy₄' (j : Fin 25) (hj : Keep j) : y₄.regs j = x.regs j :=
    (hy₄ j hj).trans (hx₄k j hj)
  have hR₄ (k : ℕ) (hk : k < r) : y₄.mem (a + k) = y₃.mem (a + k) :=
    (hfr₄ _ (by rcases hta with h | h <;> omega)).trans (congrFun hx₄m _)
  wram_exec [hy₄' R (by simp [Keep]), ha, hy₄' T (by simp [Keep]), ht]
  refine WP.name fun x₅ hx₅ => ?_
  have hx₅k (j : Fin 25) (hj : Keep j) : x₅.regs j = x.regs j := by
    rw [← hy₄' j hj]; subst hx₅
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> wram_simp
  have hx₅m : x₅.mem = y₄.mem := by subst hx₅; rfl
  obtain ⟨y₅, hy₅, ⟨hle, hiff, -⟩, -⟩ := ExecWithin.rename_post cmpMap_injective
    (Compare.exec (x₅.comap cmpMap) (a := a) (b := t) (r := r)
      (by change x₅.regs pa = a; subst hx₅; wram_simp)
      (by change x₅.regs pb = t; subst hx₅; wram_simp)
      ((hx₅k rr (by simp [Keep])).trans hr) hfa hft h1)
  refine WP.of_execWithin hy₅ ⟨?_, hle, ?_,
    fun j hj => (hy₅.regs_eq (cmp_preserves j hj)).trans (hx₅k j hj)⟩
  · rw [show powMap PolyPow.e = e from rfl, hx₃e]; unfold time; omega
  · rw [show y₅.regs flag = (y₅.comap cmpMap).regs Compare.flag from rfl, hiff,
      congruence_iff_toQuot hr0]
    change (∀ k' < r, x₅.mem (a + k') = x₅.mem (t + k')) ↔ _
    simp only [hx₅m]
    have hRred (k : ℕ) (hk : k < r) : y₄.mem (a + k) < n := by rw [hR₄ k hk]; exact hred₃ k hk
    have hTred (k : ℕ) (hk : k < r) : y₄.mem (t + k) < n := by
      rw [hT₄ k hk]; exact powAddCoeff_lt hn0 _ _ _
    rw [← toQuot_eq_toQuot_iff hn0 hr0 hRred hTred, toQuot_congr hR₄, hq₃, toQuot_congr hT₄,
      toQuot_congr hR₂, toQuot_congr hB₂, toQuot_one hr0, one_mul]

end Cslib.Algorithms.WordRAM.AKS.Congruence
