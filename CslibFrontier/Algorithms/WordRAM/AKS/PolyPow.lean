/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.AKS.PolyMul
public import CslibFrontier.Computability.WordRAM.Copy
public import Mathlib.Data.Nat.Size

/-!
# Powers modulo `X^r - 1` and `n` on the word RAM

Raising a polynomial modulo `X^r - 1` and `n` to the power `e` by repeated squaring: with a result
block `R`, a base block `B` and a scratch block `T`, each round multiplies `R` by `B` into `T` and
copies it back when `e` is odd, squares `B` into `T` and copies it back, and halves `e`. The class
of `R · B^e` is invariant, so when `e` reaches `0` the result block holds the class of
`R · B^e` for the original `R`, `B` and `e`. The loop makes `Nat.size e` rounds, each of `O(r²)`
instructions (`Cslib.Algorithms.WordRAM.AKS.PolyMul.program` and
`Cslib.WordRAM.ArrayCopy.program`). This is the polynomial arithmetic of step 5 of the AKS
algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004].

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.PolyPow.program`: the repeated-squaring loop.
* `Cslib.Algorithms.WordRAM.AKS.PolyPow.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.PolyPow.exec`: the result block receives the coefficients of
  `R · B^e` within `time r e` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.PolyPow

open Cslib.WordRAM Cslib.AKS Polynomial

/-- Base address of the result block. -/
abbrev R : Fin 21 := 0
/-- Base address of the base block. -/
abbrev B : Fin 21 := 1
/-- Base address of the scratch block. -/
abbrev T : Fin 21 := 2
/-- The number `r` of coefficients. -/
abbrev rr : Fin 21 := 3
/-- The modulus `n` of the coefficients. -/
abbrev nn : Fin 21 := 4
/-- The exponent, halved every round. -/
abbrev e : Fin 21 := 5
/-- The parity of the exponent. -/
abbrev par : Fin 21 := 6
/-- Constant two. -/
abbrev two : Fin 21 := 7
/-- Constant zero, for the loop test. -/
abbrev z : Fin 21 := 8
/-- First argument of the multiplication, and source of the copy. -/
abbrev pa : Fin 21 := 9
/-- Second argument of the multiplication, and destination of the copy. -/
abbrev pb : Fin 21 := 10
/-- Product block of the multiplication. -/
abbrev pt : Fin 21 := 11

/-- The multiplication runs on `pa`, `pb`, `pt`, `rr`, `nn` and the scratch registers `12, …, 20`.
-/
def mulMap : Fin 14 → Fin 21 := ![pa, pb, pt, rr, nn, 12, 13, 14, 15, 16, 17, 18, 19, 20]

/-- The copy runs from `pa` to `pb` over `rr` words, with scratch among `12, …, 20`. -/
def copyMap : Fin 7 → Fin 21 := ![pa, pb, rr, 12, 15, 16, 19]

theorem mulMap_injective : mulMap.Injective := by decide
theorem copyMap_injective : copyMap.Injective := by decide

/-- The multiplication touches no register below `9` other than `rr` and `nn`. -/
private theorem mulMap_ne :
    ∀ j : Fin 21, j.val < 9 → j ≠ rr → j ≠ nn → ∀ a, mulMap a ≠ j := by decide

/-- The copy touches no register below `9` other than `rr`. -/
private theorem copyMap_ne : ∀ j : Fin 21, j.val < 9 → j ≠ rr → ∀ a, copyMap a ≠ j := by decide

/-- Multiply the blocks at `x` and `y` into `T`, then copy `T` into the block at `d`. -/
def mulInto (x y d : Fin 21) : Code .standard 21 :=
  .seq (ram[ pa ← x; pb ← y; pt ← T ]) (.seq (PolyMul.program.rename mulMap)
    (.seq (ram[ pa ← T; pb ← d ]) (ArrayCopy.program.rename copyMap)))

/-- One round: multiply `R` by `B` if `e` is odd, square `B`, and halve `e`. -/
def body : Code .standard 21 := ram[
  par ← e % two; if z < par then [ ⟪mulInto R B R⟫ ] else [ par ← par ]; ⟪mulInto B B B⟫;
  e ← e / two ]

/-- Repeated squaring while the exponent is positive. -/
def program : Code .standard 21 := .seq (ram[ two ← #2; z ← #0 ]) (.loop (.lt z e) body)

/-- The instruction bound of one multiplication followed by a copy. -/
def mulTime (r : ℕ) : ℕ := 14 * (r + 1) * (r + 1) + 7 * r + 9

/-- The instruction bound of `program`: `Nat.size e` rounds of two multiplications. -/
def time (r e : ℕ) : ℕ := Nat.size e * (2 * mulTime r + 6) + 4

/-- Halving a positive number shortens its binary representation. -/
theorem size_div_two_lt {m : ℕ} (hm : 0 < m) : Nat.size (m / 2) < Nat.size m := by
  have hs : 0 < Nat.size m := Nat.size_pos.mpr hm
  have hlt : m < 2 ^ Nat.size m := Nat.lt_size_self m
  have : Nat.size (m / 2) ≤ Nat.size m - 1 := by
    rw [Nat.size_le]
    have h2 : 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  omega

private theorem mulInto_exec {w : ℕ} (X : Data 21) {x y d : Fin 21} (hx : x.val < 9)
    (hy : y.val < 9) (hd : d.val < 9) {a b t dd r n : ℕ} (ha : X.regs x = a) (hb : X.regs y = b)
    (ht : X.regs T = t) (hdd : X.regs d = dd) (hr : X.regs rr = r) (hn : X.regs nn = n)
    (hn0 : 0 < n) (hta : t + r ≤ a ∨ a + r ≤ t) (htb : t + r ≤ b ∨ b + r ≤ t)
    (htd : t + r ≤ dd ∨ dd + r ≤ t)
    (hpa : ∀ i < r, X.mem (a + i) < n) (hpb : ∀ j < r, X.mem (b + j) < n)
    (hfa : Fits w (a + r)) (hfb : Fits w (b + r)) (hft : Fits w (t + r)) (hfd : Fits w (dd + r))
    (hf2 : Fits w (2 * r)) (hfn : Fits w (n * n + n)) :
    ∃ Y, ExecWithin w (mulInto x y d) X Y (mulTime r) ∧
      (∀ k < r, Y.mem (dd + k) =
        mulCoeff n r (fun i => X.mem (a + i)) (fun j => X.mem (b + j)) k) ∧
      (∀ a', ¬(t ≤ a' ∧ a' < t + r) → ¬(dd ≤ a' ∧ a' < dd + r) → Y.mem a' = X.mem a') ∧
      (∀ j : Fin 21, j.val < 9 → Y.regs j = X.regs j) := by
  have hxa : x ≠ pa := fun h => by subst h; simp at hx
  have hya : y ≠ pa := fun h => by subst h; simp at hy
  have hda : d ≠ pa := fun h => by subst h; simp at hd
  have h1 : Fits w 1 := hfn.of_le (by nlinarith)
  wram_exec [mulInto, ha, hb, ht, hxa, hya]
  refine WP.name fun X₁ hX₁ => ?_
  have hX₁j (j : Fin 21) (hj : j.val < 9) : X₁.regs j = X.regs j := by
    have h9 : j ≠ pa ∧ j ≠ pb ∧ j ≠ pt := ⟨fun h => by subst h; simp at hj,
      fun h => by subst h; simp at hj, fun h => by subst h; simp at hj⟩
    subst hX₁; wram_simp [h9.1, h9.2.1, h9.2.2]
  have hX₁a : X₁.regs pa = a := by subst hX₁; wram_simp
  have hX₁b : X₁.regs pb = b := by subst hX₁; wram_simp
  have hX₁t : X₁.regs pt = t := by subst hX₁; wram_simp
  have hX₁r : X₁.regs rr = r := (hX₁j rr (by decide)).trans hr
  have hX₁n : X₁.regs nn = n := (hX₁j nn (by decide)).trans hn
  have hX₁m : X₁.mem = X.mem := by subst hX₁; rfl
  wram_call (PolyMul.exec (X₁.comap mulMap) hX₁a hX₁b hX₁t hX₁r hX₁n hn0 hta htb
    (hX₁m ▸ hpa) (hX₁m ▸ hpb) hfa hfb hft hf2 hfn)
    renamed mulMap_injective with Y₁ ⟨⟨hprod, hframe, -, -, -, hY₁r, hY₁n⟩, hout₁⟩
  rw [hX₁m] at hprod hframe
  have hY₁j (j : Fin 21) (hj : j.val < 9) : Y₁.regs j = X.regs j := by
    by_cases hjr : j = rr
    · exact hjr ▸ (show Y₁.regs rr = r from hY₁r).trans hr.symm
    by_cases hjn : j = nn
    · exact hjn ▸ (show Y₁.regs nn = n from hY₁n).trans hn.symm
    exact (hout₁ j (mulMap_ne j hj hjr hjn)).trans (hX₁j j hj)
  have hY₁T : Y₁.regs T = t := (hY₁j T (by decide)).trans ht
  have hY₁d : Y₁.regs d = dd := (hY₁j d hd).trans hdd
  wram_exec [hY₁T, hY₁d, hda]
  refine WP.name fun X₂ hX₂ => ?_
  have hX₂j (j : Fin 21) (hj : j.val < 9) : X₂.regs j = X.regs j := by
    have h9 : j ≠ pa ∧ j ≠ pb := ⟨fun h => by subst h; simp at hj, fun h => by subst h; simp at hj⟩
    subst hX₂; wram_simp [h9.1, h9.2, hY₁j j hj]
  have hsrc : X₂.regs pa = t := by subst hX₂; wram_simp
  have hdst : X₂.regs pb = dd := by subst hX₂; wram_simp
  have hlen : X₂.regs rr = r := (hX₂j rr (by decide)).trans hr
  have hX₂m : X₂.mem = Y₁.mem := by subst hX₂; rfl
  wram_call (ArrayCopy.exec_of_separated_or_eq (X₂.comap copyMap) h1
    (by change Fits w (X₂.regs pa + X₂.regs rr); rw [hsrc, hlen]; exact hft)
    (by change Fits w (X₂.regs pb + X₂.regs rr); rw [hdst, hlen]; exact hfd)
    (by change X₂.regs pa + X₂.regs rr ≤ X₂.regs pb ∨ X₂.regs pb + X₂.regs rr ≤ X₂.regs pa ∨
          X₂.regs pa = X₂.regs pb
        rw [hsrc, hdst, hlen]; omega))
    renamed copyMap_injective with Y₂ ⟨⟨hY₂m, -, -, hY₂len⟩, hout₂⟩
  change Y₂.mem = ArrayCopy.copyPrefix X₂.mem (X₂.regs pa) (X₂.regs pb) (X₂.regs rr) at hY₂m
  rw [hlen, hsrc, hdst, hX₂m] at hY₂m
  refine ⟨?_, fun k hk => ?_, fun a' hat had => ?_, fun j hj => ?_⟩
  · rw [show copyMap ArrayCopy.len = rr from rfl, hlen]; unfold mulTime; omega
  · rw [hY₂m, ArrayCopy.copyPrefix_read hk]; exact hprod k hk
  · rw [hY₂m, ArrayCopy.copyPrefix_outside had]; exact hframe a' hat
  · by_cases hjr : j = rr
    · exact hjr ▸ (show Y₂.regs rr = X₂.regs rr from hY₂len).trans (hlen.trans hr.symm)
    exact (hout₂ j (copyMap_ne j hj hjr)).trans (hX₂j j hj)

/-- The hypotheses of `exec` on the three blocks, the modulus and the word size. -/
private structure Hyp (w a b t r n e₀ : ℕ) : Prop where
  hn0 : 0 < n
  hab : a + r ≤ b ∨ b + r ≤ a
  hta : t + r ≤ a ∨ a + r ≤ t
  htb : t + r ≤ b ∨ b + r ≤ t
  hfa : Fits w (a + r)
  hfb : Fits w (b + r)
  hft : Fits w (t + r)
  hf2 : Fits w (2 * r)
  hfn : Fits w (n * n + n)
  hfe : Fits w e₀

/-- The loop invariant: the registers, the reduced blocks and the class of `R · B^e`. -/
private def Inv (a b t r n e₀ : ℕ) (target : AdjoinRoot (X ^ r - 1 : (ZMod n)[X]))
    (y : Data 21) : Prop :=
  y.regs R = a ∧ y.regs B = b ∧ y.regs T = t ∧ y.regs rr = r ∧ y.regs nn = n ∧ y.regs two = 2 ∧
    y.regs z = 0 ∧ y.regs e ≤ e₀ ∧ (∀ i < r, y.mem (a + i) < n) ∧ (∀ i < r, y.mem (b + i) < n) ∧
    toQuot n r (fun i => y.mem (a + i)) * toQuot n r (fun i => y.mem (b + i)) ^ y.regs e = target

private theorem body_step {w a b t r n e₀ : ℕ} (H : Hyp w a b t r n e₀)
    {target : AdjoinRoot (X ^ r - 1 : (ZMod n)[X])} (y : Data 21)
    (hy : Inv a b t r n e₀ target y) (hlt : (Cond.lt z e).Holds y) :
    ∃ y', ExecWithin w body y y' (2 * mulTime r + 4) ∧ Inv a b t r n e₀ target y' ∧
      Nat.size (y'.regs e) < Nat.size (y.regs e) := by
  obtain ⟨hyR, hyB, hyT, hyr, hyn, hy2, hyz, hye, hRred, hBred, hq⟩ := hy
  obtain ⟨E, hE⟩ : ∃ E, y.regs e = E := ⟨_, rfl⟩
  have hEpos : 0 < E := by simpa only [Cond.holds_lt, hyz, hE] using hlt
  rw [hE] at hye hq
  have h2 : Fits w 2 := H.hfn.of_le (by have := H.hn0; nlinarith)
  have hfE : Fits w E := H.hfe.of_le hye
  have hmod2 : E % 2 < 2 := Nat.mod_lt E (by norm_num)
  have hdiv2 : E / 2 ≤ E := Nat.div_le_self E 2
  wram_exec -split [body, hE, hy2]
  refine WP.cut (fun y₂ T₂ => T₂ ≤ mulTime r + 2 ∧
      (∀ j : Fin 21, j.val < 9 → j ≠ par → y₂.regs j = y.regs j) ∧
      toQuot n r (fun i => y₂.mem (a + i)) =
        toQuot n r (fun i => y.mem (a + i)) * toQuot n r (fun i => y.mem (b + i)) ^ (E % 2) ∧
      (∀ i < r, y₂.mem (a + i) < n) ∧ (∀ i < r, y₂.mem (b + i) = y.mem (b + i))) ?_ ?_
  · refine WP.name fun y₁ hy₁ => ?_
    have hy₁j (j : Fin 21) (hjp : j ≠ par) : y₁.regs j = y.regs j := by
      subst hy₁; wram_simp [hjp]
    have hz₁ : y₁.regs z = 0 := (hy₁j z (by decide)).trans hyz
    have hp₁ : y₁.regs par = E % 2 := by subst hy₁; wram_simp
    have hy₁m : y₁.mem = y.mem := by subst hy₁; rfl
    rcases Nat.mod_two_eq_zero_or_one E with hpar | hpar
    · wram_exec [hz₁, hp₁, hpar]
      refine ⟨by unfold mulTime; omega, fun j _ hjp => ?_, ?_, ?_, fun i _ => ?_⟩
      · wram_simp [hy₁j j hjp]
      · simp [Data.set_mem, hy₁m, hpar]
      · simpa [Data.set_mem, hy₁m] using hRred
      · simp [Data.set_mem, hy₁m]
    · wram_exec [hz₁, hp₁, hpar]
      wram_call (mulInto_exec (w := w) y₁ (x := R) (y := B) (d := R)
        (by decide) (by decide) (by decide)
        ((hy₁j R (by decide)).trans hyR) ((hy₁j B (by decide)).trans hyB)
        ((hy₁j T (by decide)).trans hyT) ((hy₁j R (by decide)).trans hyR)
        ((hy₁j rr (by decide)).trans hyr) ((hy₁j nn (by decide)).trans hyn)
        H.hn0 H.hta H.htb H.hta (hy₁m ▸ hRred) (hy₁m ▸ hBred)
        H.hfa H.hfb H.hft H.hfa H.hf2 H.hfn) with Y ⟨hprod, hframe, hregs⟩
      rw [hy₁m] at hprod hframe
      refine ⟨by omega, fun j hj hjp => (hregs j hj).trans (hy₁j j hjp), ?_, ?_, fun i hi => ?_⟩
      · rw [toQuot_congr hprod, toQuot_mulCoeff, hpar, pow_one]
      · intro i hi; rw [hprod i hi]; exact mulCoeff_lt H.hn0 _ _ _
      · exact hframe _ (by rcases H.htb with h | h <;> omega) (by rcases H.hab with h | h <;> omega)
  · rintro y₂ T₂ ⟨hT₂, hy₂j, hy₂R, hy₂Rred, hy₂B⟩
    refine WP.seq ?_
    wram_call (mulInto_exec (w := w) y₂ (x := B) (y := B) (d := B)
      (by decide) (by decide) (by decide)
      ((hy₂j B (by decide) (by decide)).trans hyB) ((hy₂j B (by decide) (by decide)).trans hyB)
      ((hy₂j T (by decide) (by decide)).trans hyT) ((hy₂j B (by decide) (by decide)).trans hyB)
      ((hy₂j rr (by decide) (by decide)).trans hyr) ((hy₂j nn (by decide) (by decide)).trans hyn)
      H.hn0 H.htb H.htb H.htb (fun i hi => (hy₂B i hi).trans_lt (hBred i hi))
      (fun i hi => (hy₂B i hi).trans_lt (hBred i hi))
      H.hfb H.hfb H.hft H.hfb H.hf2 H.hfn) with y₃ ⟨hprod₃, hframe₃, hregs₃⟩
    have hy₃R (i : ℕ) (hi : i < r) : y₃.mem (a + i) = y₂.mem (a + i) :=
      hframe₃ _ (by rcases H.hta with h | h <;> omega) (by rcases H.hab with h | h <;> omega)
    have hy₃j (j : Fin 21) (hj : j.val < 9) (hjp : j ≠ par) : y₃.regs j = y.regs j :=
      (hregs₃ j hj).trans (hy₂j j hj hjp)
    have hy₃e : y₃.regs e = E := (hy₃j e (by decide) (by decide)).trans hE
    have hy₃2 : y₃.regs two = 2 := (hy₃j two (by decide) (by decide)).trans hy2
    wram_exec [hy₃e, hy₃2]
    wram_simp [Inv, hy₃j R (by decide) (by decide), hyR, hy₃j B (by decide) (by decide), hyB,
      hy₃j T (by decide) (by decide), hyT, hy₃j rr (by decide) (by decide), hyr,
      hy₃j nn (by decide) (by decide), hyn, hy₃2, hy₃j z (by decide) (by decide), hyz, hE,
      Data.set_mem]
    refine ⟨⟨hdiv2.trans hye, fun i hi => (hy₃R i hi).trans_lt (hy₂Rred i hi),
      fun i hi => (hprod₃ i hi).trans_lt (mulCoeff_lt H.hn0 _ _ _), ?_⟩, size_div_two_lt hEpos⟩
    rw [toQuot_congr hy₃R, toQuot_congr hprod₃, toQuot_mulCoeff, toQuot_congr hy₂B, hy₂R, ← hq,
      ← sq, ← pow_mul, mul_assoc, ← pow_add, Nat.mod_add_div]

/-- **Powers modulo `X^r - 1` and `n`.** If the result, base and scratch blocks `[a, a + r)`,
`[b, b + r)` and `[t, t + r)` are pairwise disjoint, the result and base coefficients are below
`n ≥ 1`, and the word size holds the block ends, `2 r`, `n² + n` and the exponent `e`, then within
`time r e` instructions the result block receives reduced coefficients whose class is that of
`R · B^e`. -/
theorem exec {w : ℕ} (x : Data 21) {a b t r n : ℕ} (ha : x.regs R = a) (hb : x.regs B = b)
    (ht : x.regs T = t) (hr : x.regs rr = r) (hn : x.regs nn = n) (hn0 : 0 < n)
    (hab : a + r ≤ b ∨ b + r ≤ a) (hta : t + r ≤ a ∨ a + r ≤ t) (htb : t + r ≤ b ∨ b + r ≤ t)
    (hpa : ∀ i < r, x.mem (a + i) < n) (hpb : ∀ i < r, x.mem (b + i) < n)
    (hfa : Fits w (a + r)) (hfb : Fits w (b + r)) (hft : Fits w (t + r)) (hf2 : Fits w (2 * r))
    (hfn : Fits w (n * n + n)) (hfe : Fits w (x.regs e)) :
    ∃ y, ExecWithin w program x y (time r (x.regs e)) ∧
      toQuot n r (fun i => y.mem (a + i)) =
        toQuot n r (fun i => x.mem (a + i)) * toQuot n r (fun i => x.mem (b + i)) ^ x.regs e ∧
      (∀ i < r, y.mem (a + i) < n) ∧ y.regs R = a ∧ y.regs B = b ∧ y.regs T = t ∧
      y.regs rr = r ∧ y.regs nn = n := by
  have H : Hyp w a b t r n (x.regs e) := ⟨hn0, hab, hta, htb, hfa, hfb, hft, hf2, hfn, hfe⟩
  have h2 : Fits w 2 := hfn.of_le (by nlinarith)
  wram_exec [program]
  refine WP.name fun x₀ hx₀ => ?_
  have hx₀e : x₀.regs e = x.regs e := by subst hx₀; wram_simp
  have hI : Inv a b t r n (x.regs e) (toQuot n r (fun i => x.mem (a + i)) *
      toQuot n r (fun i => x.mem (b + i)) ^ x.regs e) x₀ := by
    subst hx₀
    simp only [Inv]
    wram_simp [ha, hb, ht, hr, hn, Data.set_mem]
    exact ⟨le_rfl, hpa, hpb⟩
  obtain ⟨y, hrun, ⟨hyR, hyB, hyT, hyr, hyn, -, hyz, -, hRred, -, hq⟩, hc⟩ :=
    ExecWithin.loop_invariant _ (fun y => Nat.size (y.regs e)) (body_step H) hI
  have hy0 : y.regs e = 0 := by simp only [Cond.holds_lt, hyz] at hc; omega
  refine WP.of_execWithin hrun ⟨?_, ?_, hRred, hyR, hyB, hyT, hyr, hyn⟩
  · rw [hx₀e, show 2 * mulTime r + 4 + 2 = 2 * mulTime r + 6 by ring]
    unfold time
    omega
  · rw [← hq, hy0, pow_zero, mul_one]

end Cslib.Algorithms.WordRAM.AKS.PolyPow
