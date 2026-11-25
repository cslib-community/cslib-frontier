/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.CountCall
import Mathlib.Tactic.FinCases
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Native collision counts for the three Chan–He sets

All three calls are actual native counting programs, with charged argument and result copies.
The prime-search control registers and every input cell below the workspace are preserved.

## Main definitions

* `CountTriple.program`: three complete native collision-count calls.

## Main results

* `CountTriple.exec`: exact counts for all three sets and charged total time.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountTriple

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Run one full count call on each of the three arrays. -/
def program : Code .standard 64 :=
  .seq (CountCall.program 0) (.seq (CountCall.program 1) (CountCall.program 2))

/-- Count collisions in all three injectively enumerated sets in at most
`34(n₀+n₁+n₂)+15M+72` instructions, excluding halt. All caller registers except the
three results are preserved, as is all memory before the counting workspace. -/
theorem exec {w M : ℕ} (x : Data 64) (values : Fin 3 → ℕ → ℤ) (hM : 0 < M)
    (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmodreg : x.regs CountCall.modulus = encode (M : ℤ))
    (hfit : ∀ j i, i < x.regs (CountCall.length j) → GenericRAM.Signed.Fits w (values j i))
    (hs : ∀ j, Fits (w + 2) (x.regs (CountCall.source j) + x.regs (CountCall.length j)))
    (hk : ∀ j, Fits (w + 2) (x.regs CountCall.scratch + x.regs (CountCall.length j)))
    (hd : Fits (w + 2) (x.regs CountCall.histogram + M))
    (ht : ∀ j, Fits (w + 2) (x.regs (CountCall.length j) * x.regs (CountCall.length j) +
      x.regs (CountCall.length j) + 1))
    (hsk : ∀ j, x.regs (CountCall.source j) + x.regs (CountCall.length j) ≤
      x.regs CountCall.scratch)
    (hkd : ∀ j, x.regs CountCall.scratch + x.regs (CountCall.length j) ≤
      x.regs CountCall.histogram)
    (hinput : ∀ j i, i < x.regs (CountCall.length j) →
      x.mem (x.regs (CountCall.source j) + i) = encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (CountCall.length j))) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y
        (34 * (x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
          x.regs (CountCall.length 2)) + 15 * M + 72) ∧
      (∀ j, y.regs (CountCall.result j) = Cslib.Algorithms.ThreeSum.ChanHe.coll
        ((Finset.range (x.regs (CountCall.length j))).image (values j)) M) ∧
      (∀ i, (28 ≤ i.val ∧ i.val < 37) ∨ 40 ≤ i.val → y.regs i = x.regs i) ∧
      ∀ a < x.regs CountCall.scratch, y.mem a = x.mem a := by
  let P (i : Fin 64) : Prop := (28 ≤ i.val ∧ i.val < 37) ∨ 40 ≤ i.val
  let R (y : Data 64) : Prop := (∀ i, P i → y.regs i = x.regs i) ∧
    ∀ a < x.regs CountCall.scratch, y.mem a = x.mem a
  have hcall (j : Fin 3) (y : Data 64) (hy : R y) :
      ∃ z, ExecWithin (w + 2) (CountCall.program j) y z
          (34 * x.regs (CountCall.length j) + 5 * M + 24) ∧ R z ∧
        z.regs (CountCall.result j) = Cslib.Algorithms.ThreeSum.ChanHe.coll
          ((Finset.range (x.regs (CountCall.length j))).image (values j)) M ∧
        ∀ i, 28 ≤ i.val → i ≠ CountCall.result j → z.regs i = y.regs i := by
    obtain ⟨hr, hm⟩ := hy
    have hl : y.regs (CountCall.length j) = x.regs (CountCall.length j) :=
      hr _ (by dsimp [P, CountCall.length]; omega)
    have hb : y.regs (CountCall.source j) = x.regs (CountCall.source j) :=
      hr _ (by dsimp [P, CountCall.source]; omega)
    have hws : y.regs CountCall.scratch = x.regs CountCall.scratch := hr _ (by decide)
    have hwh : y.regs CountCall.histogram = x.regs CountCall.histogram := hr _ (by decide)
    have hwm : y.regs CountCall.modulus = encode (M : ℤ) := by regs_frame
    obtain ⟨z, he, hzm, hzv, hzr⟩ := CountCall.exec j y (values j) hM hmod hwm
      (by simpa only [hl] using hfit j) (by simpa only [hb, hl] using hs j)
      (by simpa only [hws, hl] using hk j) (by simpa only [hwh] using hd)
      (by simpa only [hl] using ht j) (by simpa only [hb, hl, hws] using hsk j)
      (by simpa only [hws, hl, hwh] using hkd j)
      (fun i hi => by
        rw [hb, hm _ (by have := hsk j; omega)]; exact hinput j i (hl ▸ hi))
      (by simpa only [hl] using hinj j)
    refine ⟨z, by simpa only [hl] using he, ⟨fun i hi => (hzr i (by dsimp [P] at hi; omega)
      fun heq => ?_).trans (hr i hi), fun a ha => ?_⟩, by simpa only [hl] using hzv, hzr⟩
    · have := congrArg Fin.val heq
      dsimp [P, CountCall.result] at *
      omega
    · rw [hzm, Count.memory_before]
      · exact hm a ha
      · simpa only [hws] using ha
      · have := hkd j; rw [hwh]; omega
  have hx : R x := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨a, ha, hRa, hva, hfa⟩ := hcall 0 x hx
  obtain ⟨b, hb, hRb, hvb, hfb⟩ := hcall 1 a hRa
  obtain ⟨c, hc, hRc, hvc, hfc⟩ := hcall 2 b hRb
  exact ⟨c, (ha.seq (hb.seq hc)).mono (by omega), fun j => by fin_cases j <;> regs_frame, hRc⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountTriple
