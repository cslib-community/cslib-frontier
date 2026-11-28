/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Foundations.NumberTheory.AKS.Coefficients
import CslibFrontier.Computability.WordRAM.SymbolicExec.ListLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame

/-!
# Writing and comparing coefficient arrays on the word RAM

Two linear-time array routines for polynomials modulo `X^r - 1` and `n`, stored as `r` words:
`Fill` writes the coefficients `Cslib.AKS.powAddCoeff n r e a` of `X^e + a` (it clears the block
and then adds `a` at index `0` and `1` at index `e mod r`), and `Compare` tests two blocks for
equality.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.Fill.program`: write the coefficients of `X^e + a`.
* `Cslib.Algorithms.WordRAM.AKS.Compare.program`: compare two blocks.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.Fill.exec`: the block receives `Cslib.AKS.powAddCoeff` within
  `5 r + 13` instructions, and no other cell changes.
* `Cslib.Algorithms.WordRAM.AKS.Compare.exec`: the flag is `1` exactly when the blocks agree,
  within `11 r + 5` instructions, and memory is unchanged.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS

open Cslib.WordRAM

namespace Fill

/-- Base address of the block. -/
abbrev base : Fin 10 := 0
/-- The number `r` of coefficients. -/
abbrev rr : Fin 10 := 1
/-- The modulus `n`. -/
abbrev nn : Fin 10 := 2
/-- The index `e mod r` of the monomial. -/
abbrev er : Fin 10 := 3
/-- The constant term `a`. -/
abbrev aa : Fin 10 := 4
/-- Loop index. -/
abbrev i : Fin 10 := 5
/-- Address scratch. -/
abbrev addr : Fin 10 := 6
/-- Value scratch. -/
abbrev t : Fin 10 := 7
/-- Constant one. -/
abbrev one : Fin 10 := 8
/-- Constant zero. -/
abbrev zero : Fin 10 := 9

/-- Clear one cell. -/
def clearBody : Code .standard 10 := ram[ addr ← base + i; *addr ← zero; i ← i + one ]

/-- Store `a mod n` at index `0`. -/
def storeConst : Code .standard 10 := ram[ t ← aa % nn; *base ← t ]

/-- Add `1` at index `e mod r`, modulo `n`. -/
def addMonomial : Code .standard 10 := ram[
  addr ← base + er; t ← *addr; t ← t + one; t ← t % nn; *addr ← t ]

/-- Store `a mod n` at index `0`, then add `1` at index `e mod r`. -/
def finish : Code .standard 10 := .seq storeConst addMonomial

/-- Clear the block, then write the two nonzero coefficients. -/
def program : Code .standard 10 :=
  .seq (ram[ one ← #1; zero ← #0; i ← #0 ]) (.seq (.loop (.lt i rr) clearBody) finish)

/-- **Writing `X^e + a`.** For `r ≥ 1` and `n ≥ 1`, with `e mod r` in `er` and the block end,
`a`, `n` and `n + 1` fitting a word, the block `[b, b + r)` receives the coefficients
`Cslib.AKS.powAddCoeff n r e a` within `5 r + 13` instructions, and no other cell changes. -/
theorem exec {w : ℕ} (x : Data 10) {b r n e a : ℕ} (hb : x.regs base = b) (hr : x.regs rr = r)
    (hn : x.regs nn = n) (her : x.regs er = e % r) (ha : x.regs aa = a) (hr0 : 0 < r)
    (hn0 : 0 < n) (hfb : Fits w (b + r)) (hfa : Fits w a) (hfn : Fits w (n + 1)) :
    ∃ y, ExecWithin w program x y (5 * r + 13) ∧
      (∀ k < r, y.mem (b + k) = Cslib.AKS.powAddCoeff n r e a k) ∧
      (∀ a', ¬(b ≤ a' ∧ a' < b + r) → y.mem a' = x.mem a') ∧
      y.regs base = b ∧ y.regs rr = r ∧ y.regs nn = n := by
  have _ := hfa
  have hclear : ∃ y, ExecWithin w (.loop (.lt i rr) clearBody)
      (((x.set one 1).set zero 0).set i 0) y (5 * r + 2) ∧
      y.mem = fun a' => if b ≤ a' ∧ a' < b + r then 0 else x.mem a' := by
    wram_fold (fun rest y => y.regs i + rest.length = r ∧
        ∀ a', y.mem a' = if b ≤ a' ∧ a' < b + y.regs i then 0 else x.mem a')
      over (List.replicate r ()) cost (fun _ => 3)
    case init =>
      exact ⟨by wram_simp; simp, fun a' => by wram_simp; exact (ite_eq_right (by omega)).symm⟩
    case exit =>
      rintro v m hI; rw [hr]; omega
    case step =>
      rintro _ as v m hI
      have hfit' (u : ℕ) (hu : u ≤ b + r) : Fits w u := hfb.of_le hu
      refine ⟨by rw [hr]; omega, ?_⟩
      unfold clearBody
      wram_exec [hb, hfit']
      refine ⟨by wram_simp; omega, fun a' => ?_⟩
      by_cases ha' : a' = b + v i
      · subst ha'; wram_simp; exact (ite_eq_left (by omega)).symm
      · refine Eq.trans (by mem_frame : _ = m a') ?_
        rw [hI.2 a']; wram_simp; congr 1; exact propext ⟨by omega, by omega⟩
    case post =>
      rintro v m hI
      refine ⟨by simp; omega, funext fun a' => ?_⟩
      rw [hI.2 a']; congr 1; exact propext ⟨by omega, by omega⟩
  have her' : e % r < r := Nat.mod_lt _ hr0
  have hamod : a % n < n := Nat.mod_lt _ hn0
  set c := if e % r = 0 then a % n else 0 with hc
  have hcn : c < n := by rw [hc]; split_ifs <;> omega
  have hfc1 : Fits w (c + 1) := hfn.of_le (by omega)
  have hcm : (c + 1) % n < n := Nat.mod_lt _ hn0
  unfold program finish storeConst addMonomial
  wram_exec
  wram_call hclear framed with v₁ m₁ rfl
  have hcell : (((Data.havoc (.loop (.lt i rr) clearBody) (((x.set one 1).set zero 0).set i 0) v₁
      fun a' => if b ≤ a' ∧ a' < b + r then 0 else x.mem a').set t (a % n)).write b (a % n)).mem
      (b + e % r) = c := by
    by_cases h : e % r = 0
    · wram_simp [h]; simp [hc, h]
    · refine Eq.trans (by mem_frame : _ = _) ?_
      simp [hc, h, her']
  wram_exec [hb, hr, hn, her, ha, hcell, hfc1]
  refine ⟨?_, ?_, by wram_simp [hb], by wram_simp [hr], by wram_simp [hn]⟩
  · intro k hk
    by_cases hke : k = e % r
    · subst hke
      wram_simp [hcell]
      simp only [Cslib.AKS.powAddCoeff, ↓reduceIte, hc]
      split_ifs with h0
      · rw [Nat.mod_add_mod, Nat.add_comm]
      · simp
    · by_cases hk0 : k = 0
      · subst hk0
        refine Eq.trans (by mem_frame : _ = (((Data.havoc _ _ v₁ _).set t (a % n)).write b
          (a % n)).mem (b + 0)) ?_
        wram_simp
        simp [Cslib.AKS.powAddCoeff, hke]
      · refine Eq.trans (by mem_frame : _ = (if b ≤ b + k ∧ b + k < b + r then 0
          else x.mem (b + k))) ?_
        simp [Cslib.AKS.powAddCoeff, hke, hk0, hk]
  · intro a' ha'
    refine Eq.trans (by mem_frame : _ = (if b ≤ a' ∧ a' < b + r then 0 else x.mem a')) ?_
    exact ite_eq_right ha'

end Fill

namespace Compare

/-- Base address of the first block. -/
abbrev p : Fin 9 := 0
/-- Base address of the second block. -/
abbrev q : Fin 9 := 1
/-- The number `r` of coefficients. -/
abbrev rr : Fin 9 := 2
/-- Loop index. -/
abbrev k : Fin 9 := 3
/-- Address scratch. -/
abbrev addr : Fin 9 := 4
/-- Coefficient of the first block. -/
abbrev u : Fin 9 := 5
/-- Coefficient of the second block. -/
abbrev v : Fin 9 := 6
/-- The answer: `1` when the blocks agree. -/
abbrev flag : Fin 9 := 7
/-- Constant one. -/
abbrev one : Fin 9 := 8

/-- Compare one pair of coefficients. -/
def body : Code .standard 9 := ram[
  addr ← p + k; u ← *addr; addr ← q + k; v ← *addr;
  if u = v then [ flag ← flag ] else [ flag ← #0 ]; k ← k + one ]

/-- Compare two blocks of `r` words. -/
def program : Code .standard 9 :=
  .seq (ram[ flag ← #1; one ← #1; k ← #0 ]) (.loop (.lt k rr) body)

/-- **Comparing blocks.** With both block ends fitting a word, the program leaves `1` in `flag`
exactly when the blocks `[a, a + r)` and `[b, b + r)` agree, and `0` otherwise, within
`11 r + 5` instructions, without changing memory. -/
theorem exec {w : ℕ} (x : Data 9) {a b r : ℕ} (ha : x.regs p = a) (hb : x.regs q = b)
    (hr : x.regs rr = r) (hfa : Fits w (a + r)) (hfb : Fits w (b + r)) (h1 : Fits w 1) :
    ∃ y, ExecWithin w program x y (11 * r + 5) ∧ y.regs flag ≤ 1 ∧
      (y.regs flag = 1 ↔ ∀ k' < r, x.mem (a + k') = x.mem (b + k')) ∧ y.mem = x.mem := by
  classical
  unfold program
  wram_exec
  wram_fold (fun rest y => y.regs k + rest.length = r ∧ y.mem = x.mem ∧
      y.regs flag = if ∀ k' < y.regs k, x.mem (a + k') = x.mem (b + k') then 1 else 0)
    over (List.replicate r ()) cost (fun _ => 9)
  case init =>
    exact ⟨by wram_simp; simp, rfl, by wram_simp; simp⟩
  case exit =>
    rintro v m hI; rw [hr]; omega
  case step =>
    rintro _ as v m ⟨hk, rfl, hfl⟩
    have hf1 (t : ℕ) (ht : t ≤ a + r) : Fits w t := hfa.of_le ht
    have hf2 (t : ℕ) (ht : t ≤ b + r) : Fits w t := hfb.of_le ht
    have hiff : (∀ k' < v k + 1, x.mem (a + k') = x.mem (b + k')) ↔
        (∀ k' < v k, x.mem (a + k') = x.mem (b + k')) ∧ x.mem (a + v k) = x.mem (b + v k) :=
      ⟨fun h => ⟨fun k' hk' => h k' (by omega), h (v k) (by omega)⟩,
        fun ⟨h, hK⟩ k' hk' => (Nat.lt_succ_iff_lt_or_eq.mp hk').elim (h k') (· ▸ hK)⟩
    refine ⟨by rw [hr]; omega, ?_⟩
    unfold body
    wram_exec [ha, hb, hf1, hf2] <;>
      exact ⟨by wram_simp; omega, by wram_simp, by wram_simp [hfl, hiff]; simp [hc]⟩
  case post =>
    rintro v m ⟨hk, rfl, hfl⟩
    have hkr : v k = r := by omega
    rw [hkr] at hfl
    refine ⟨by simp; omega, by rw [hfl]; split_ifs <;> omega, ?_, rfl⟩
    rw [hfl]; split_ifs with h; exacts [iff_of_true (by simp) h, iff_of_false (by simp) h]

end Compare

end Cslib.Algorithms.WordRAM.AKS
