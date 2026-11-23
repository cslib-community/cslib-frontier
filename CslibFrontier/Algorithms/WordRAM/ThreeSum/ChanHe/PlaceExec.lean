/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.Place

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged execution of the native Chan–He placement scan

## Main results

* `Place.tagged_encode`: the unsigned sign/magnitude calculation is the exact tagged integer.

## References

The encoding calculation and native proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The encoded tagged value can be computed without a signed primitive. The positive tag
dominates the integer magnitude, so unsigned subtraction cannot truncate a negative result. -/
theorem tagged_encode (neg : Bool) (z : ℤ) (t : ℕ) (ht : z.natAbs ≤ t) :
    encode (signedValue neg z + (t : ℤ)) =
      if encode z % 2 = (if neg then 1 else 0) then
        2 * t + (encode z / 2 + encode z / 2)
      else 2 * t - (encode z / 2 + encode z / 2) := by
  have hbounds : (z.natAbs : ℤ) = z ∨ (z.natAbs : ℤ) = -z := by
    rcases Int.natAbs_eq z with h | h <;> [exact Or.inl h.symm; exact Or.inr (by omega)]
  have hnon : ¬(signedValue neg z + (t : ℤ) < 0) := by
    cases neg <;> simp only [signedValue, Bool.false_eq_true, ↓reduceIte] <;>
      rcases hbounds with h | h <;> omega
  simp only [encode_mod_two, encode_div_two]
  rw [encode, ite_eq_right hnon]
  have hm := Int.natAbs_of_nonneg (Int.not_lt.mp hnon)
  cases neg <;> by_cases hz : z < 0 <;>
    simp only [signedValue, hz, Bool.false_eq_true, Nat.reduceEqDiff, ↓reduceIte] at hm ⊢ <;>
    rcases hbounds with h | h <;> omega

/-- A polynomial envelope for every value and address produced by the placement scan.
The caller supplies a fit for this sum; no fit of an uncomputed output is assumed. -/
def budget (x : Data 32) (M N U t : ℕ) : ℕ :=
  x.regs src + x.regs keys + x.regs hist + x.regs heavy + x.regs packed + x.regs len +
    M + 4 * N + 2 * t + 2 * U + 16


/-- One complete scan round, including classification, sign/tag work, both light stores,
heavy count maintenance and the input cursor increment. -/
theorem exec_body {w M N U t : ℕ} (x : Data 32) (values : ℕ → ℤ) (neg : Bool)
    (hM : 0 < M) (hN : 2 * M ≤ N) (hc : x.regs column < 4)
    (hd : x.regs distance ≤ 4 * M) (ht : U ≤ t)
    (hmod : x.regs modulus = M) (htag : x.regs tag = 2 * t)
    (hneg : x.regs negative = if neg then 1 else 0)
    (h1 : x.regs one = 1) (h2 : x.regs two = 2) (h4 : x.regs four = 4)
    (h0 : x.regs zero = 0) (hi : x.regs idx < x.regs len)
    (hcount : x.regs count = (heavyList values (x.regs len) M (x.regs idx)).length)
    (hbdd : (values (x.regs idx)).natAbs ≤ U)
    (hfit : Fits w (budget x M N U t))
    (hinput : x.mem (x.regs src + x.regs idx) = encode (values (x.regs idx)))
    (hkey : x.mem (x.regs keys + x.regs idx) = residueKey M (values (x.regs idx)))
    (hhist : x.mem (x.regs hist + residueKey M (values (x.regs idx))) =
      Histogram.count (fun j => residueKey M (values j)) (x.regs len)
        (residueKey M (values (x.regs idx)))) :
    ∃ y, ExecWithin w body x y 30 ∧
      y.mem = write x.mem values (x.regs len) M (x.regs heavy) (x.regs packed)
        (x.regs column) (x.regs distance) t neg (x.regs idx) ∧
      y.regs count = (heavyList values (x.regs len) M (x.regs idx + 1)).length ∧
      y.regs idx = x.regs idx + 1 ∧
      (∀ i, (9 ≤ i.val ∧ i.val ≤ 19) ∨ i = one ∨ i = two ∨ i = four ∨ i = zero →
        y.regs i = x.regs i) := by
  have hpres : ∀ i : Fin 32,
      (9 ≤ i.val ∧ i.val ≤ 19) ∨ i = one ∨ i = two ∨ i = four ∨ i = zero →
        body.Preserves i := by decide +kernel
  have hr : residueKey M (values (x.regs idx)) < M := residueKey_lt hM _
  have hhl := length_heavyList_le values (x.regs len) M (x.regs idx)
  have hmodr := Nat.mod_lt (M - residueKey M (values (x.regs idx))) hM
  have hmod2 := Nat.mod_lt (encode (values (x.regs idx))) (by decide : 0 < 2)
  have hv := tagged_encode neg (values (x.regs idx)) t (hbdd.trans ht)
  have hcp : 0 < Histogram.count (fun j => residueKey M (values j)) (x.regs len)
      (residueKey M (values (x.regs idx))) := count_residue_pos values _ M hi
  dsimp only [budget] at hfit
  obtain ⟨y, he, hym, hyc, hyi⟩ : ∃ y, ExecWithin w body x y 30 ∧
      y.mem = write x.mem values (x.regs len) M (x.regs heavy) (x.regs packed)
        (x.regs column) (x.regs distance) t neg (x.regs idx) ∧
      y.regs count = (heavyList values (x.regs len) M (x.regs idx + 1)).length ∧
      y.regs idx = x.regs idx + 1 := by
    by_cases hh : 1 < Histogram.count (fun j => residueKey M (values j)) (x.regs len)
        (residueKey M (values (x.regs idx)))
    · refine WP.exists_execWithin ?_
      unfold body heavyCode
      wram_exec [h1, hinput, hkey, hhist, hh]
      exact ⟨by wram_simp; simp [write, hh, hcount],
        by wram_simp [hcount]; simp [heavyList, hh], by wram_simp⟩
    · have hc1 : Histogram.count (fun j => residueKey M (values j)) (x.regs len)
          (residueKey M (values (x.regs idx))) = 1 := by omega
      cases neg <;> by_cases hs : values (x.regs idx) < 0
      all_goals
        refine WP.exists_execWithin ?_
        unfold body lightCode
        wram_exec [h1, h2, h4, h0, hmod, htag, hneg, hinput, hkey, hhist, hh, hc1, hs,
          encode_div_two, encode_mod_two]
        refine ⟨?_, by wram_simp [hcount]; simp [heavyList, hh], by wram_simp⟩
        wram_simp
        simp only [write, hh, ↓reduceIte]
        simp +decide [targetKey, hs, encode_div_two, encode_mod_two, hv]
  exact ⟨y, he, hym, hyc, hyi, fun i hi => he.regs_eq (hpres i hi)⟩


/-- Complete native placement in at most `32n+8` instructions, excluding halt. All input,
residue and histogram reads are proved from the memory frame, rather than assumed anew at
iterations. The heavy block precedes the packed block, which precedes the counting workspace. -/
theorem exec {w M N U t : ℕ} (x : Data 32) (values : ℕ → ℤ) (neg : Bool)
    (hM : 0 < M) (hN : 2 * M ≤ N) (hc : x.regs column < 4)
    (hd : x.regs distance ≤ 4 * M) (ht : U ≤ t)
    (hmod : x.regs modulus = M) (htag : x.regs tag = 2 * t)
    (hneg : x.regs negative = if neg then 1 else 0)
    (hbdd : ∀ i < x.regs len, (values i).natAbs ≤ U)
    (hfit : Fits w (budget x M N U t))
    (hsh : x.regs src + x.regs len ≤ x.regs heavy)
    (hhp : x.regs heavy + x.regs len ≤ x.regs packed)
    (hpk : x.regs packed + 4 * N ≤ x.regs keys)
    (hkh : x.regs keys + x.regs len ≤ x.regs hist)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i))
    (hkey : ∀ i < x.regs len, x.mem (x.regs keys + i) = residueKey M (values i))
    (hhist : ∀ r < M, x.mem (x.regs hist + r) =
      Histogram.count (fun j => residueKey M (values j)) (x.regs len) r) :
    ∃ y, ExecWithin w program x y (32 * x.regs len + 8) ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs heavy) (x.regs packed)
        (x.regs column) (x.regs distance) t neg (x.regs len) ∧
      y.regs count = (heavyList values (x.regs len) M (x.regs len)).length ∧
      ∀ i, 9 ≤ i.val ∧ i.val ≤ 19 → y.regs i = x.regs i := by
  let P (i : Fin 32) : Prop := 9 ≤ i.val ∧ i.val ≤ 19
  let Inv (j : ℕ) (y : Data 32) : Prop :=
    (∀ i, P i → y.regs i = x.regs i) ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
      y.regs four = 4 ∧ y.regs zero = 0 ∧
      y.regs count = (heavyList values (x.regs len) M j).length ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs heavy) (x.regs packed)
        (x.regs column) (x.regs distance) t neg j
  have hbody (y : Data 32) (hy : Inv (y.regs idx) y) (hlt : y.regs idx < x.regs len) :
      ∃ z, ExecWithin w body y z 30 ∧ Inv (y.regs idx + 1) z ∧ z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, h1, h2, h4, h0, hcount, hm⟩ := hy
    have hs := hr src (by decide)
    have hk := hr keys (by decide)
    have hl := hr len (by decide)
    have hh := hr hist (by decide)
    have ho := hr heavy (by decide)
    have hp := hr packed (by decide)
    have hcol := hr column (by decide)
    have hdist := hr distance (by decide)
    have hmod' := (hr modulus (by decide)).trans hmod
    have htag' := (hr tag (by decide)).trans htag
    have hneg' := (hr negative (by decide)).trans hneg
    have hbefore (a : ℕ) (ha : a < x.regs heavy) : y.mem a = x.mem a := by
      rw [hm]
      apply memory_outside _ _ _ _ _ _ _ _ _ N neg hM hN hc hd hlt.le <;> omega
    have hafter (a : ℕ) (ha : x.regs keys ≤ a) : y.mem a = x.mem a := by
      rw [hm]
      apply memory_outside _ _ _ _ _ _ _ _ _ N neg hM hN hc hd hlt.le <;> omega
    obtain ⟨z, he, hzm, hzc, hzi, hzr⟩ := exec_body y values neg hM hN
      (by simpa only [hcol] using hc) (by simpa only [hdist] using hd) ht hmod' htag' hneg'
      h1 h2 h4 h0 (by simpa only [hl] using hlt) (by simpa only [hl] using hcount)
      (hbdd _ hlt)
      (by simpa only [budget, hs, hk, hh, ho, hp, hl] using hfit)
      (by rw [hs, hbefore _ (by omega)]; exact hinput _ hlt)
      (by rw [hk, hafter _ (by omega)]; exact hkey _ hlt)
      (by rw [hh, hl, hafter _ (by omega)]; exact hhist _ (residueKey_lt hM _))
    refine ⟨z, he, ?_, hzi⟩
    refine ⟨fun i hi => (hzr i (Or.inl hi)).trans (hr i hi),
      (hzr one (by simp)).trans h1,
      (hzr two (by simp)).trans h2, (hzr four (by simp)).trans h4,
      (hzr zero (by simp)).trans h0,
      by simpa only [hl] using hzc, ?_⟩
    rw [hzm, hl, ho, hp, hcol, hdist, hm]
    rfl
  have f4 : Fits w 4 := hfit.of_le (by dsimp only [budget]; omega)
  refine WP.exists_execWithin ?_
  unfold program
  wram_exec
  wram_call (ExecWithin.loop_count Inv (fun _ hy => hy.1 len (by decide)) hbody
    (by wram_simp; omega) ⟨fun i hi => by
      dsimp only [P] at hi
      simp only [Data.set_regs, Function.update_apply, Fin.ext_iff,
        idx, count, one, two, four, zero]
      split_ifs <;> omega,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp [heavyList, List.length_nil], by wram_simp [memory]⟩)
    with y ⟨⟨hr, _, _, _, _, hcount, hm⟩, _⟩
  exact ⟨by wram_simp; omega, hm, hcount, hr⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place
