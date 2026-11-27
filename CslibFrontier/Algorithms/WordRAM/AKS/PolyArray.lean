/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Foundations.NumberTheory.AKS.Coefficients
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec

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

private theorem clear_step {w b r : ℕ} {m : ℕ → ℕ} (hfb : Fits w (b + r)) (y : Data 10)
    (hy : y.regs base = b ∧ y.regs rr = r ∧ y.regs one = 1 ∧ y.regs zero = 0 ∧
      ∀ a', y.mem a' = if b ≤ a' ∧ a' < b + y.regs i then 0 else m a')
    (hc : y.regs i < r) :
    ∃ z, ExecWithin w clearBody y z 3 ∧
      (z.regs base = b ∧ z.regs rr = r ∧ z.regs one = 1 ∧ z.regs zero = 0 ∧
        ∀ a', z.mem a' = if b ≤ a' ∧ a' < b + (y.regs i + 1) then 0 else m a') ∧
      z.regs i = y.regs i + 1 := by
  obtain ⟨hyb, hyr, hyo, hyz, hym⟩ := hy
  unfold clearBody
  wram_exec [hyb, hyr, hyo, hyz]
  wram_simp [hyb, hyr, hyo, hyz, Data.write_mem, Data.set_mem]
  intro a'
  rw [Function.update_apply, hym]
  split_ifs <;> first | rfl | omega

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
  let P (j : ℕ) (y : Data 10) : Prop :=
    y.regs base = b ∧ y.regs rr = r ∧ y.regs one = 1 ∧ y.regs zero = 0 ∧
      ∀ a', y.mem a' = if b ≤ a' ∧ a' < b + j then 0 else x.mem a'
  unfold program
  wram_exec
  refine WP.name fun x₀ hx₀ => ?_
  have hi₀ : x₀.regs i = 0 := by subst hx₀; wram_simp
  have hx₀P : P (x₀.regs i) x₀ := by
    subst hx₀
    refine ⟨?_, ?_, ?_, ?_, fun a' => ?_⟩
    · wram_simp [hb]
    · wram_simp [hr]
    · wram_simp
    · wram_simp
    · wram_simp [Data.set_mem]
      split_ifs <;> first | rfl | omega
  obtain ⟨y, hrun₁, ⟨hyb, hyr, hyo, -, hym⟩, _⟩ := ExecWithin.loop_count P
    (fun _ hy => hy.2.1) (clear_step hfb) (by omega) hx₀P
  have hyn : y.regs nn = n :=
    (hrun₁.regs_eq (by decide)).trans (by subst hx₀; wram_simp [hn])
  have hya : y.regs aa = a :=
    (hrun₁.regs_eq (by decide)).trans (by subst hx₀; wram_simp [ha])
  have hye : y.regs er = e % r :=
    (hrun₁.regs_eq (by decide)).trans (by subst hx₀; wram_simp [her])
  have her' : e % r < r := Nat.mod_lt _ hr0
  have hamod : a % n < n := Nat.mod_lt _ hn0
  obtain ⟨c, hc⟩ : ∃ c, c = if e % r = 0 then a % n else 0 := ⟨_, rfl⟩
  have hcn : c < n := by rw [hc]; split_ifs <;> omega
  have hcm : (c + 1) % n < n := Nat.mod_lt _ hn0
  refine WP.of_execWithin hrun₁ ?_
  unfold finish storeConst
  wram_exec [hya, hyn, hyb]
  refine WP.name fun y' hy' => ?_
  have hy'm : y'.mem = Function.update y.mem b (a % n) := by subst hy'; rfl
  have hcell : y'.mem (b + e % r) = c := by
    rw [hy'm]
    by_cases h : e % r = 0
    · simp [hc, h]
    · rw [Function.update_of_ne (by omega), hym]
      simp [hc, h, show b + e % r < b + r by omega]
  have hy'b : y'.regs base = b := by subst hy'; wram_simp [hyb]
  have hy'e : y'.regs er = e % r := by subst hy'; wram_simp [hye]
  have hy'o : y'.regs one = 1 := by subst hy'; wram_simp [hyo]
  have hy'n : y'.regs nn = n := by subst hy'; wram_simp [hyn]
  have hy'r : y'.regs rr = r := by subst hy'; wram_simp [hyr]
  unfold addMonomial
  wram_exec [hy'b, hy'e, hy'o, hy'n, hcell]
  wram_simp [hy'b, hy'r, hy'n, hi₀, Data.write_mem, Data.set_mem]
  refine ⟨fun k hk => ?_, fun a' ha' => ?_⟩
  · by_cases hke : k = e % r
    · subst hke
      rw [Function.update_self]
      simp only [Cslib.AKS.powAddCoeff, ↓reduceIte, hc]
      split_ifs with h0
      · rw [Nat.mod_add_mod, Nat.add_comm]
      · simp
    · rw [Function.update_of_ne (by omega), hy'm]
      by_cases hk0 : k = 0
      · subst hk0
        simp only [Nat.add_zero, Function.update_self, Cslib.AKS.powAddCoeff, hke, ↓reduceIte,
          Nat.zero_add]
      · rw [Function.update_of_ne (by omega), hym]
        simp [Cslib.AKS.powAddCoeff, hke, hk0, show b + k < b + r by omega]
  · rw [Function.update_of_ne (by omega), hy'm, Function.update_of_ne (by omega), hym]
    simp [ha']

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

private theorem step {w a b r : ℕ} {m : ℕ → ℕ} (hfa : Fits w (a + r)) (hfb : Fits w (b + r))
    (y : Data 9)
    (hy : y.regs p = a ∧ y.regs q = b ∧ y.regs rr = r ∧ y.regs one = 1 ∧
      y.mem = m ∧ (y.regs flag = if ∀ k' < y.regs k, m (a + k') = m (b + k') then 1 else 0))
    (hlt : y.regs k < r) :
    ∃ z, ExecWithin w body y z 9 ∧
      (z.regs p = a ∧ z.regs q = b ∧ z.regs rr = r ∧ z.regs one = 1 ∧
        z.mem = m ∧ (z.regs flag = if ∀ k' < y.regs k + 1, m (a + k') = m (b + k') then 1 else 0)) ∧
      z.regs k = y.regs k + 1 := by
  classical
  obtain ⟨hya, hyb, hyr, hyo, hym, hyf⟩ := hy
  have hiff : (∀ k' < y.regs k + 1, m (a + k') = m (b + k')) ↔
      (∀ k' < y.regs k, m (a + k') = m (b + k')) ∧ m (a + y.regs k) = m (b + y.regs k) := by
    constructor
    · intro h; exact ⟨fun k' hk' => h k' (by omega), h (y.regs k) (by omega)⟩
    · rintro ⟨h, hK'⟩ k' hk'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
      · exact h k' hk'
      · exact hK'
  unfold body
  wram_exec [hya, hyb, hyo, hym] <;>
    { wram_simp [hya, hyb, hyr, hyo, hym, hyf, hiff]; simp [hc] }

/-- **Comparing blocks.** With both block ends fitting a word, the program leaves `1` in `flag`
exactly when the blocks `[a, a + r)` and `[b, b + r)` agree, and `0` otherwise, within
`11 r + 5` instructions, without changing memory. -/
theorem exec {w : ℕ} (x : Data 9) {a b r : ℕ} (ha : x.regs p = a) (hb : x.regs q = b)
    (hr : x.regs rr = r) (hfa : Fits w (a + r)) (hfb : Fits w (b + r)) (h1 : Fits w 1) :
    ∃ y, ExecWithin w program x y (11 * r + 5) ∧ y.regs flag ≤ 1 ∧
      (y.regs flag = 1 ↔ ∀ k' < r, x.mem (a + k') = x.mem (b + k')) ∧ y.mem = x.mem := by
  classical
  let P (j : ℕ) (y : Data 9) : Prop :=
    y.regs p = a ∧ y.regs q = b ∧ y.regs rr = r ∧ y.regs one = 1 ∧ y.mem = x.mem ∧
      (y.regs flag = if ∀ k' < j, x.mem (a + k') = x.mem (b + k') then 1 else 0)
  unfold program
  wram_exec
  refine WP.name fun x₀ hx₀ => ?_
  have hk₀ : x₀.regs k = 0 := by subst hx₀; wram_simp
  have hx₀P : P (x₀.regs k) x₀ := by
    subst hx₀; simp only [P]; wram_simp [ha, hb, hr]; simp
  obtain ⟨y, hrun₁, ⟨-, -, -, -, hym, hyf⟩, _⟩ := ExecWithin.loop_count P
    (fun _ ⟨_, _, hrr, _⟩ => hrr) (step hfa hfb) (by omega) hx₀P
  refine WP.of_execWithin hrun₁ ⟨by omega, ?_, ?_, hym⟩
  · rw [hyf]; split_ifs <;> omega
  · rw [hyf]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => rfl⟩
    · exact ⟨fun h' => by simp at h', fun h' => absurd h' h⟩

end Compare

end Cslib.Algorithms.WordRAM.AKS
