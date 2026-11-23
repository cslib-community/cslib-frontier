/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged in-place normalization of an array

`ArrayNormalize.program` replaces each word of a supplied interval by its remainder modulo a
supplied positive modulus. It executes actual loads, remainders and stores; the untouched
memory need not already be normalized. This small topic module avoids adding an application
specific transformation to the allocation API.
-/

public section

namespace Cslib.WordRAM.ArrayNormalize

/-- First address to normalize. -/
abbrev base : Fin 7 := 0
/-- Number of words. -/
abbrev length : Fin 7 := 1
/-- Positive normalization modulus. -/
abbrev modulus : Fin 7 := 2
/-- Current index. -/
abbrev index : Fin 7 := 3
/-- Temporary absolute address. -/
abbrev address : Fin 7 := 4
/-- Loaded and normalized word. -/
abbrev value : Fin 7 := 5
/-- Constant one. -/
abbrev one : Fin 7 := 6

/-- Normalize one cell with five actual native instructions. -/
@[expose] def body : Code .standard 7 := ram[
  address ← base + index; value ← *address; value ← value % modulus;
  *address ← value; index ← index + one ]

/-- Fixed code for in-place normalization of an interval supplied in registers. -/
@[expose] def program : Code .standard 7 :=
  .seq (ram[ index ← #0; one ← #1 ]) (.loop (.lt index length) body)

/-- Mathematical memory after normalizing a prefix; this is not a machine operation. -/
def normalizePrefix (mem : ℕ → ℕ) (b M k : ℕ) : ℕ → ℕ :=
  fun a => if b ≤ a ∧ a < b + k then mem a % M else mem a

/-- Every cell in the normalized interval contains its original remainder. -/
theorem normalizePrefix_read (mem : ℕ → ℕ) (b M n j : ℕ) (hj : j < n) :
    normalizePrefix mem b M n (b + j) = mem (b + j) % M := by
  simp [normalizePrefix, hj]

/-- Normalizing an interval leaves all outside memory unchanged. -/
theorem normalizePrefix_outside (mem : ℕ → ℕ) (b M n a : ℕ)
    (ha : ¬(b ≤ a ∧ a < b + n)) : normalizePrefix mem b M n a = mem a := by
  simp [normalizePrefix, ha]

private theorem normalizePrefix_succ (mem : ℕ → ℕ) (b M k : ℕ) :
    normalizePrefix mem b M (k + 1) =
      Function.update (normalizePrefix mem b M k) (b + k) (mem (b + k) % M) := by
  funext a
  by_cases ha : a = b + k
  · subst a; simp [normalizePrefix]
  · simp only [normalizePrefix, Function.update_of_ne ha,
      show (b ≤ a ∧ a < b + (k + 1)) ↔ (b ≤ a ∧ a < b + k) by omega]

private theorem normalizePrefix_zero (mem : ℕ → ℕ) (b M : ℕ) :
    normalizePrefix mem b M 0 = mem := by
  funext a; simp [normalizePrefix]

/-- In-place normalization costs at most `7n+4` native instructions, including every indexed
load/store and loop decision. The input arguments and all outside memory are preserved. -/
theorem exec {W b M n : ℕ} (x : Data 7) (hb : x.regs base = b)
    (hn : x.regs length = n) (hm : x.regs modulus = M) (hM : 0 < M)
    (hfit : Fits W (b + n + M + 2)) :
    ∃ y, ExecWithin W program x y (7 * n + 4) ∧ y.mem = normalizePrefix x.mem b M n ∧
      y.regs base = b ∧ y.regs length = n ∧ y.regs modulus = M := by
  unfold program
  wram_exec
  let P (j : ℕ) (y : Data 7) : Prop := y.regs base = b ∧ y.regs length = n ∧
    y.regs modulus = M ∧ y.regs one = 1 ∧ y.mem = normalizePrefix x.mem b M j
  refine WP.of_spec (ExecWithin.loop_count (N := n) (T := 5) P (fun _ hy => hy.2.1) ?_ ?_ ?_) ?_
  · rintro y ⟨yb, yn, ym, yo, ymem⟩ hlt
    have hread : y.mem (b + y.regs index) = x.mem (b + y.regs index) := by
      rw [ymem]; simp [normalizePrefix]
    unfold body
    wram_exec [yb, ym, yo, hread]
    dsimp only [P]
    wram_simp [yb, yn, ym, yo, ymem, ← normalizePrefix_succ]
  · wram_simp [Nat.zero_le]
  · dsimp only [P]; wram_simp [hb, hn, hm, normalizePrefix_zero]
  · rintro y ⟨⟨hyb, hyn, hym, _, hymem⟩, _⟩
    exact ⟨by wram_simp; omega, hymem, hyb, hyn, hym⟩

end Cslib.WordRAM.ArrayNormalize
