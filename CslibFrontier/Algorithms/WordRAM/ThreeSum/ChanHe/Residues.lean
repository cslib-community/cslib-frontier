/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Signed.Arithmetic
public import CslibFrontier.Computability.WordRAM.Copy

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc

/-!
# Native Euclidean residue arrays

The input holds signed encodings. The output holds ordinary unsigned residue keys, ready
for histogram construction. In particular a nonnegative encoded integer is explicitly decoded
by division by two before it is used as a histogram index.

## Main definitions

* `Residues.program`: a fixed loop producing Euclidean residue keys.

## Main results

* `Residues.exec`: charged execution preserving the input and all cells outside the output.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Residues

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Encoded integer input base. -/
abbrev src : Fin 16 := 9
/-- Unsigned residue output base. -/
abbrev dst : Fin 16 := 10
/-- Input length. -/
abbrev len : Fin 16 := 11
/-- Encoded modulus. -/
abbrev modulus : Fin 16 := 12
/-- Loop counter. -/
abbrev idx : Fin 16 := 13
/-- Address scratch. -/
abbrev addr : Fin 16 := 14
/-- Constant one. -/
abbrev one : Fin 16 := 15

/-- The signed remainder block followed by explicit unsigned decoding and a store. -/
def body : Code .standard 16 :=
  .seq (ram[ addr ← src + idx; left ← *addr; right ← modulus ])
    (.seq Signed.modulo (ram[ two ← #2; result ← result / two;
      addr ← dst + idx; *addr ← result; idx ← idx + one ]))

/-- All parameters are supplied at runtime; registers and code are independent
of length and width. -/
def program : Code .standard 16 :=
  .seq (ram[ idx ← #0; one ← #1 ]) (.loop (.lt idx len) body)

/-- Memory after writing a prefix of unsigned residue keys. -/
def memory (mem : ℕ → ℕ) (values : ℕ → ℤ) (M dst k : ℕ) : ℕ → ℕ :=
  fun a => if dst ≤ a ∧ a < dst + k then (values (a - dst) % (M : ℤ)).toNat else mem a

@[simp] theorem memory_zero (mem : ℕ → ℕ) (values : ℕ → ℤ) (M dst : ℕ) :
    memory mem values M dst 0 = mem := by
  funext a
  simp [memory]

private theorem memory_succ (mem : ℕ → ℕ) (values : ℕ → ℤ) (M dst k : ℕ) :
    memory mem values M dst (k + 1) = Function.update (memory mem values M dst k)
      (dst + k) (values k % (M : ℤ)).toNat := by
  funext a
  by_cases ha : a = dst + k
  · subst a
    simp [memory]
  · rw [Function.update_of_ne ha]
    simp only [memory]
    have h : (dst ≤ a ∧ a < dst + (k + 1)) ↔ (dst ≤ a ∧ a < dst + k) := by omega
    simp only [h]

/-- Convert `n` encoded signed integers to unsigned Euclidean residue keys in at most
`23n + 4` native instructions. The modulus is positive and encoded in its parameter register;
addresses are ordinary unsigned words. The final halt is excluded. -/
theorem exec {w M : ℕ} (x : Data 16) (values : ℕ → ℤ) (hM : 0 < M)
    (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmodreg : x.regs modulus = encode (M : ℤ))
    (hfit : ∀ i < x.regs len, GenericRAM.Signed.Fits w (values i))
    (hs : Fits (w + 2) (x.regs src + x.regs len))
    (hd : Fits (w + 2) (x.regs dst + x.regs len))
    (hdisj : x.regs src + x.regs len ≤ x.regs dst)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i)) :
    ∃ y, ExecWithin (w + 2) program x y (23 * x.regs len + 4) ∧
      y.mem = memory x.mem values M (x.regs dst) (x.regs len) ∧
      (∀ i, 9 ≤ i.val ∧ i.val ≤ 12 → y.regs i = x.regs i) := by
  let P (j : ℕ) (y : Data 16) : Prop :=
    (∀ i, 9 ≤ i.val ∧ i.val ≤ 12 → y.regs i = x.regs i) ∧ y.regs one = 1 ∧
      y.mem = memory x.mem values M (x.regs dst) j
  have hbody (y : Data 16) (hy : P (y.regs idx) y) (hlt : y.regs idx < x.regs len) :
      ∃ z, ExecWithin (w + 2) body y z 21 ∧ P (y.regs idx + 1) z ∧ z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, ho, hm⟩ := hy
    have hsrc := hr src (by decide)
    have hdst := hr dst (by decide)
    have hmod' := hr modulus (by decide)
    have hread : y.mem (y.regs src + y.regs idx) = encode (values (y.regs idx)) := by
      rw [hm, hsrc]
      simp only [memory, show ¬(x.regs dst ≤ x.regs src + y.regs idx ∧
        x.regs src + y.regs idx < x.regs dst + y.regs idx) from by omega, ↓reduceIte]
      exact hinput _ hlt
    have ha : Fits (w + 2) (y.regs src + y.regs idx) := hs.of_le (by rw [hsrc]; omega)
    have hnonneg := Int.emod_nonneg (values (y.regs idx)) (show (M : ℤ) ≠ 0 by omega)
    have hrem : Fits (w + 2) (values (y.regs idx) % (M : ℤ)).toNat := by
      have hlt' := Int.emod_lt_of_pos (values (y.regs idx)) (show (0 : ℤ) < M by omega)
      exact ((encode_fits hmod).mono (by omega)).of_le (by
        simp only [encode, Int.natAbs_natCast, show ¬(M : ℤ) < 0 from by omega, ↓reduceIte]
        omega)
    have htwo : Fits (w + 2) 2 := (show Fits 2 2 from by decide).mono (by omega)
    refine WP.exists_execWithin ?_
    wram_exec [body, ha, hread, hmod', hmodreg]
    wram_call (Signed.exec_modulo (hfit _ hlt) hmod _ (by wram_simp) (by wram_simp))
      framed with v m ⟨hzval, hzmem, _⟩
    wram_simp at hzmem
    have hdecode : v result / 2 = (values (y.regs idx) % (M : ℤ)).toNat := by
      rw [hzval, GenericRAM.Signed.Arithmetic.eval, encode_div_two]
      omega
    have hpres : ∀ i : Fin 16, 9 ≤ i.val ∧ i.val ≤ 12 → Signed.modulo.Preserves i :=
      by decide +kernel
    wram_exec [htwo, hrem, ho, hdecode, hdst]
    refine ⟨⟨fun i hi => ?_, by wram_simp [ho],
      by wram_simp [hzmem, hm, ← memory_succ]⟩, by wram_simp⟩
    simp only [Data.set_regs, Data.write_regs, Function.update_apply, Fin.ext_iff,
      two, result, addr, idx,
      Data.havoc_regs_of_preserves (hpres i hi), hr i hi]
    split_ifs <;> omega
  have h1 : Fits (w + 2) 1 := (show Fits 2 1 from by decide).mono (by omega)
  refine WP.exists_execWithin ?_
  wram_exec [program, h1]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1 len (by decide)) hbody
    (by wram_simp; omega) ⟨fun i hi => by
      simp only [Data.set_regs, Function.update_apply, Fin.ext_iff, idx, one]
      split_ifs <;> omega,
      by wram_simp, by wram_simp [memory_zero]⟩)
    with y ⟨⟨hr, _, hm⟩, _⟩
  exact ⟨by wram_simp; omega, hm, hr⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Residues
