/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.NatGcd
public import Mathlib.Data.Nat.Totient

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Step 3 of the AKS algorithm and Euler's totient on the word RAM

Step 3 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] outputs COMPOSITE if
`1 < gcd(a, n) < n` for some `a ≤ r`, and step 5 needs `φ(r)`. One loop over `0 ≤ a ≤ r` does
both, with two runs of Euclid's algorithm (`Cslib.Algorithms.WordRAM.NatGcd.program`) per `a`: it
clears a flag when `gcd(n, a)` is neither `1` nor `n`, and counts the `a` with `gcd(r, a) = 1`.
The index `a = 0` is harmless (`gcd(n, 0) = n`), and for `r ≥ 2` neither `0` nor `r` is coprime
to `r`, so the count is `φ(r)`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.GcdTotient.program`: the loop.
* `Cslib.Algorithms.WordRAM.AKS.GcdTotient.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.GcdTotient.exec`: the flag records step 3 and the count is `φ(r)`,
  within `time r` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.GcdTotient

open Cslib.WordRAM

/-- The number `n`, preserved. -/
abbrev n : Fin 11 := 0
/-- The modulus `r`, preserved. -/
abbrev r : Fin 11 := 1
/-- The loop index `a`. -/
abbrev a : Fin 11 := 2
/-- The loop end `r + 1`. -/
abbrev lim : Fin 11 := 3
/-- `1` while every `gcd(n, a)` seen is `1` or `n`. -/
abbrev ok : Fin 11 := 4
/-- The number of `a` seen with `gcd(r, a) = 1`. -/
abbrev phi : Fin 11 := 5
/-- Constant one. -/
abbrev one : Fin 11 := 6
/-- First argument of the gcd, and its result. -/
abbrev ga : Fin 11 := 7
/-- Second argument of the gcd. -/
abbrev gb : Fin 11 := 8

/-- Euclid's algorithm runs on `ga`, `gb` and two scratch registers. -/
def gcdMap : Fin 4 → Fin 11 := ![ga, gb, 9, 10]

theorem gcdMap_injective : gcdMap.Injective := by decide

/-- The gcd on `ga` and `gb`. -/
def gcd : Code .standard 11 := NatGcd.program.rename gcdMap

/-- Test `gcd(n, a)`, count `gcd(r, a) = 1`, and advance `a`. -/
def body : Code .standard 11 :=
  .seq (ram[ ga ← n; gb ← a ]) (.seq gcd
    (.seq (ram[ if ga = one then [ ok ← ok ] else [ if ga = n then [ ok ← ok ] else [ ok ← #0 ] ];
      ga ← r; gb ← a ]) (.seq gcd
    (ram[ if ga = one then [ phi ← phi + one ] else [ phi ← phi ]; a ← a + one ]))))

/-- Run the body for `a = 0, 1, …, r`. -/
def program : Code .standard 11 :=
  .seq (ram[ one ← #1; lim ← r + one; a ← #0; ok ← #1; phi ← #0 ]) (.loop (.lt a lim) body)

/-- The instruction bound of `program`. -/
def time (r : ℕ) : ℕ := (r + 1) * (10 * r + 21) + 7

/-- Counting the residues coprime to `r ≥ 2` up to `r` inclusive gives `φ(r)`. -/
private theorem card_filter_coprime_range_succ {R : ℕ} (hR : 2 ≤ R) :
    ((Finset.range (R + 1)).filter R.Coprime).card = Nat.totient R := by
  rw [Finset.range_add_one, Finset.filter_insert]
  simp [Nat.coprime_self, show R ≠ 1 by omega, Nat.totient_eq_card_coprime]

/-- The semantic prefix of the gcd/totient scan after processing `j` values. -/
private def Inv (N R j : ℕ) (y : Data 11) : Prop :=
  y.regs n = N ∧ y.regs r = R ∧ y.regs one = 1 ∧ y.regs lim = R + 1 ∧
    y.regs ok ≤ 1 ∧ (y.regs ok = 1 ↔ ∀ b < j, Nat.gcd N b = 1 ∨ Nat.gcd N b = N) ∧
    y.regs phi = ((Finset.range j).filter R.Coprime).card

private theorem body_step {w N R : ℕ} (hfN : Fits w N) (hfR : Fits w (R + 1)) (y : Data 11)
    (hy : Inv N R (y.regs a) y) (hlt : y.regs a < R + 1) :
    ∃ z, ExecWithin w body y z (10 * R + 19) ∧
      Inv N R (y.regs a + 1) z ∧ z.regs a = y.regs a + 1 := by
  classical
  obtain ⟨hyn, hyr, hy1, hyl, hyok, hyiff, hyphi⟩ := hy
  obtain ⟨A, hA⟩ : ∃ A, y.regs a = A := ⟨_, rfl⟩
  have hAR : A ≤ R := by rw [hA] at hlt; omega
  rw [hA] at hyiff hyphi
  have hkeep : ∀ j ∈ [n, r, a, lim, ok, phi, one], (∀ i, gcdMap i ≠ j) ∧ j ≠ ga ∧ j ≠ gb := by
    decide
  unfold body gcd
  wram_exec [hyn, hA]
  refine WP.name fun y₁ hy₁ => ?_
  have hy₁a : y₁.regs ga = N := by subst hy₁; wram_simp
  have hy₁b : y₁.regs gb = A := by subst hy₁; wram_simp
  wram_call (NatGcd.exec (y₁.comap gcdMap)
    (by change Fits w (y₁.regs ga); exact hy₁a ▸ hfN)
    (by change Fits w (y₁.regs gb); exact hy₁b ▸ hfR.of_le (by omega)))
    renamed gcdMap_injective with y₂ ⟨⟨hg₂, -⟩, hout₂⟩
  have hg₂' : y₂.regs ga = Nat.gcd N A := by
    change y₂.regs ga = (y₁.regs ga).gcd (y₁.regs gb) at hg₂
    rwa [hy₁a, hy₁b] at hg₂
  have hy₂ {j : Fin 11} (hj : j ∈ [n, r, a, lim, ok, phi, one]) : y₂.regs j = y.regs j := by
    obtain ⟨h1, h2, h3⟩ := hkeep j hj
    rw [hout₂ j h1]; subst hy₁; wram_simp [h2, h3]
  have hy₂n : y₂.regs n = N := (hy₂ (by simp)).trans hyn
  have hy₂r : y₂.regs r = R := (hy₂ (by simp)).trans hyr
  have hy₂a : y₂.regs a = A := (hy₂ (by simp)).trans hA
  have hy₂l : y₂.regs lim = R + 1 := (hy₂ (by simp)).trans hyl
  have hy₂ok : y₂.regs ok = y.regs ok := hy₂ (by simp)
  have hy₂p : y₂.regs phi = ((Finset.range A).filter R.Coprime).card :=
    (hy₂ (by simp)).trans hyphi
  have hy₂1 : y₂.regs one = 1 := (hy₂ (by simp)).trans hy1
  let o := if Nat.gcd N A = 1 ∨ Nat.gcd N A = N then y.regs ok else 0
  refine WP.seq ?_
  refine WP.cut (fun y₃ T₃ => T₃ ≤ 7 ∧ y₃.regs ga = R ∧
      y₃.regs gb = A ∧ y₃.regs n = N ∧ y₃.regs r = R ∧ y₃.regs a = A ∧
      y₃.regs lim = R + 1 ∧ y₃.regs ok = o ∧
      y₃.regs phi = ((Finset.range A).filter R.Coprime).card ∧ y₃.regs one = 1) ?_ ?_
  · wram_exec [hg₂', hy₂1, hy₂n, hy₂ok, hy₂r, hy₂a] <;>
      { wram_simp [hy₂n, hy₂r, hy₂a, hy₂l, hy₂ok, hy₂p, hy₂1]; dsimp [o]; simp_all }
  · rintro y₃ T₃ ⟨hT₃, hy₃ga, hy₃gb, hy₃n, hy₃r, hy₃a, hy₃l, hy₃ok, hy₃p, hy₃1⟩
    wram_exec
    wram_call (NatGcd.exec (y₃.comap gcdMap)
      (by change Fits w (y₃.regs ga); exact hy₃ga ▸ hfR.of_le (by omega))
      (by change Fits w (y₃.regs gb); exact hy₃gb ▸ hfR.of_le (by omega)))
      renamed gcdMap_injective with y₄ ⟨⟨hg₄, -⟩, hout₄⟩
    have hg₄' : y₄.regs ga = Nat.gcd R A := by
      change y₄.regs ga = (y₃.regs ga).gcd (y₃.regs gb) at hg₄
      rwa [hy₃ga, hy₃gb] at hg₄
    have hy₄n : y₄.regs n = N := (hout₄ n (by decide)).trans hy₃n
    have hy₄r : y₄.regs r = R := (hout₄ r (by decide)).trans hy₃r
    have hy₄a : y₄.regs a = A := (hout₄ a (by decide)).trans hy₃a
    have hy₄l : y₄.regs lim = R + 1 := (hout₄ lim (by decide)).trans hy₃l
    have hy₄ok : y₄.regs ok = o := (hout₄ ok (by decide)).trans hy₃ok
    have hy₄p : y₄.regs phi = ((Finset.range A).filter R.Coprime).card :=
      (hout₄ phi (by decide)).trans hy₃p
    have hy₄1 : y₄.regs one = 1 := (hout₄ one (by decide)).trans hy₃1
    have hphiA : ((Finset.range A).filter R.Coprime).card ≤ A :=
      (Finset.card_filter_le _ _).trans (Finset.card_range A).le
    have ho_le : o ≤ 1 := by dsimp [o]; split_ifs <;> omega
    have ho_iff : o = 1 ↔ ∀ b < A + 1, Nat.gcd N b = 1 ∨ Nat.gcd N b = N := by
      dsimp [o]
      constructor
      · intro h b hb
        split_ifs at h with hc'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
        · exact hyiff.mp h b hb
        · exact hc'
      · intro h
        simp only [h A (by omega), ↓reduceIte]
        exact hyiff.mpr fun b hb => h b (by omega)
    wram_exec [hg₄', hy₄1, hy₄p, hy₄a]
    · have hcard : ((Finset.range (A + 1)).filter R.Coprime).card =
          ((Finset.range A).filter R.Coprime).card + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert]
        simp [Nat.Coprime, hc]
      wram_simp [Inv, hy₄n, hy₄r, hy₄1, hy₄l, hy₄ok, hy₄p, hA, hcard, ho_le, ho_iff]
      rw [show gcdMap NatGcd.b = gb from rfl, hy₁b, hy₃gb]; omega
    · have hcard : ((Finset.range (A + 1)).filter R.Coprime).card =
          ((Finset.range A).filter R.Coprime).card := by
        rw [Finset.range_add_one, Finset.filter_insert]
        simp [Nat.Coprime, hc]
      wram_simp [Inv, hy₄n, hy₄r, hy₄1, hy₄l, hy₄ok, hy₄p, hA, hcard, ho_le, ho_iff]
      rw [show gcdMap NatGcd.b = gb from rfl, hy₁b, hy₃gb]; omega

/-- **Step 3 and the totient.** For `r ≥ 2`, with the word size holding `n` and `r + 1`, within
`time r` instructions the flag `ok` is `1` exactly when every `1 ≤ a ≤ r` has `gcd(a, n) = 1` or
`gcd(a, n) = n`, and `phi` is `φ(r)`. For `n ≥ 1` the flag condition says that no `1 ≤ a ≤ r` has
`1 < gcd(a, n) < n`; for `n = 0` it is stronger, since `gcd(a, 0) = a`. -/
theorem exec {w : ℕ} (x : Data 11) {N R : ℕ} (hn : x.regs n = N) (hr : x.regs r = R)
    (hR : 2 ≤ R) (hfN : Fits w N) (hfR : Fits w (R + 1)) :
    ∃ y, ExecWithin w program x y (time R) ∧ y.regs ok ≤ 1 ∧
      (y.regs ok = 1 ↔ ∀ b, 1 ≤ b → b ≤ R → b.gcd N = 1 ∨ b.gcd N = N) ∧
      y.regs phi = Nat.totient R ∧ y.regs n = N ∧ y.regs r = R := by
  unfold program
  wram_exec [hr]
  refine WP.name fun x₀ hx₀ => ?_
  have ha₀ : x₀.regs a = 0 := by subst hx₀; wram_simp
  have hx₀I : Inv N R (x₀.regs a) x₀ := by
    subst hx₀; simp only [Inv]; wram_simp [hn, hr]; simp
  obtain ⟨y, hrun, ⟨hyn, hyr, _, _, hyok, hyiff, hyphi⟩, _⟩ :=
    ExecWithin.loop_count (Inv N R) (fun _ ⟨_, _, _, hlim, _⟩ => hlim)
      (body_step hfN hfR) (by omega) hx₀I
  refine WP.of_execWithin hrun ⟨?_, hyok, ?_, ?_, hyn, hyr⟩
  · rw [ha₀, Nat.sub_zero, show 10 * R + 19 + 2 = 10 * R + 21 by ring]
    unfold time
    omega
  · rw [hyiff]
    constructor
    · intro h b hb1 hbR
      rw [Nat.gcd_comm]
      exact h b (by omega)
    · intro h b hb
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · right; exact Nat.gcd_zero_right N
      · rw [Nat.gcd_comm]; exact h b hb0 (by omega)
  · rw [hyphi, card_filter_coprime_range_succ hR]

end Cslib.Algorithms.WordRAM.AKS.GcdTotient
