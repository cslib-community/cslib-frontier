/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the fits tactic)

public import CslibFrontier.Tactic.Fits
public import CslibFrontier.Computability.WordRAM.ExactNotation
public import CslibFrontier.Computability.GenericRAM.Signed

/-!
# Tests for `fits`
-/

public section

open Cslib.WordRAM

variable {w a b c n : ℕ}

/-! A bound follows from any word-size fact in context, whatever its name. -/

example (hfit_end : Fits w (n + 5)) (h : a ≤ n) : Fits w (a + 3) := by
  fits

example (h₁ : Fits w a) (h₂ : Fits w b) (h : c ≤ a ∨ c ≤ b) : Fits w c := by
  fits

example : Fits w n → Fits w (n / 2) := by
  intro
  fits

/-! Constants, shifts and powers of two, as in the address and mask computations of programs. -/

example (h : Fits w (n + 2)) : Fits w 0 ∧ Fits w 1 ∧ Fits w 2 := by
  fits

example (hb : Fits w (2 ^ c)) : Fits w (2 ^ c - 1) := by
  fits

example (h : Fits w (2 * a + 1)) : Fits w (a <<< 1) := by
  fits

/-- A wider word: `omega` reads `2 ^ (w + 1)` as `2 * 2 ^ w`. -/
example (h : Fits w n) : Fits (w + 1) (2 * n + 1) := by
  fits

/-! The unfolded form `v < 2 ^ w`, in the goal or in a hypothesis. -/

example (h : Fits w n) : n - 1 < 2 ^ w := by
  fits

example (h : n < 2 ^ w) (ha : a ≤ n) : Fits w a := by
  fits

/-! Hypotheses that combine word-size facts. -/

example (h : Fits w a ∧ Fits w b) : Fits w (min a b) ∧ Fits w (max a b) := by
  fits

example (h : ¬Fits w a) (hb : a ≤ b) : ¬Fits w b := by
  fits

/-! Products are atoms: give a bound on one as a term. -/

example (h : Fits w (a * b)) (hc : c ≤ a) : Fits w (c * b) := by
  fits [Nat.mul_le_mul_right b hc]

/-! A side condition inline, as an argument. -/

example (h : Fits w (n + 1)) : Fits w n ∧ Fits w (n + 1) :=
  ⟨by fits, h⟩

/-! Sibling goals stay pending. -/

set_option linter.style.multiGoal false in
example (h : Fits w n) : Fits w (n - 1) ∧ Nonempty ℕ := by
  constructor
  fits
  exact ⟨0⟩

/-! `ram_eval` and `ram_exact_eval` decide which written values fit a word with `fits`
(`reduceFits`), so a bound that follows from a fact in context needs no statement of its own. -/

/-- A register name for the examples. -/
abbrev r0 : Fin 2 := 0
/-- A register name for the examples. -/
abbrev r1 : Fin 2 := 1

example (x : Data 2) (hx : x.regs r0 = n) (hfit : Fits w (2 * n + 1)) :
    ExecWithin w ram[ r1 ← r0 + r0 ] x (x.set r1 (n + n)) 1 := by
  ram_eval [hx]

example (x : Data 2) (hx : x.regs r0 = n) (hfit : Fits w (2 * n + 1)) :
    Exec w ram_exact[ r1 ← r0 + r0 ] x (x.set r1 (n + n)) 1 := by
  ram_exact_eval [hx]

/-- Without a fact that implies the bound, the value is not known to fit and evaluation is stuck. -/
example (x : Data 2) (_hx : x.regs r0 = n) (_hfit : Fits w n) :
    ExecWithin w ram[ r1 ← r0 + r0 ] x (x.set r1 (n + n)) 1 ∨ True := by
  fail_if_success (left; ram_eval [_hx])
  exact Or.inr trivial

/-! Non-linear, bitwise, power-of-two, `Fin.isLt`, `Data.Bounded`, and `Signed.Fits` bounds. -/

example (h : Fits w a) : Fits w (a / b) := by fits
example (h : Fits w a) : Fits w (a % b) := by fits
example (k : ℕ) (hk : k ≤ w) : Fits w (a % 2 ^ k) := by fits
example (hb : 0 < b) (h : Fits w b) : Fits w (a % b) := by fits
example (h : Fits w a) : Fits w (a - b) := by fits
example (h : Fits w a) : Fits w (a &&& b) := by fits
example (h : Fits w b) : Fits w (a &&& b) := by fits
example (k : ℕ) (hk : k ≤ w) : Fits w (a &&& (2 ^ k - 1)) := by fits
example (h : Fits w a) : Fits w (a >>> b) := by fits
example (ha : Fits w a) (hb : Fits w b) : Fits w (a ^^^ b) := by fits
example (ha : Fits w a) (hb : Fits w b) : Fits w (a ||| b) := by fits
example {q : ℕ} (hq : q ≤ w) (ha : a < 2 ^ q) (hb : b < 2 ^ q) (hc : c < 2 ^ q) :
    Fits w ((a ^^^ b) ^^^ c) := by fits
example {q : ℕ} (hq : q ≤ w) (ha : a < 2 ^ q) (hb : b < 2 ^ q) (hc : c < 2 ^ q) :
    Fits w ((a ||| b) ||| c) := by fits
example : Fits w w := by fits
example {m : ℕ} (hm : m ≤ w) : Fits w (m - c) := by fits
example {w₀ : ℕ} (hw : w₀ ≤ w) : Fits w (2 ^ (w₀ - 1) - 1) := by fits
example {q : ℕ} (hq : 0 < q) (hw : 2 * q ≤ w) : Fits w (2 ^ q) := by fits
example {w₀ : ℕ} (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w) : Fits w 2 := by fits
example (hw : 4 ≤ w) : Fits w 15 := by fits
example {w₀ : ℕ} (hw₀ : 0 < w₀) (hb : a < 2 ^ (w₀ - 1)) : 2 * a + 1 < 2 ^ w₀ := by fits
example {w₀ : ℕ} (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w) (hb : a < 2 ^ (w₀ - 1)) (hc : c < 2 ^ w₀) :
    Fits w ((2 * a + 1) * c) := by fits
example {u b : ℕ} (hu : u < 2 ^ b) : u <<< b < 2 ^ (2 * b) := by fits
example {m : ℕ} (i : Fin (2 ^ m)) (hm : m ≤ w) : Fits w i.val := by fits
example {m : ℕ} (i j : Fin (2 ^ m)) (hm : m ≤ w) : Fits w (i.val ^^^ j.val) := by fits
example (x : Data 2) (hx : x.Bounded w) : Fits w (x.regs r0) := by fits
example (x : Data 2) (hx : x.Bounded w) (addr : ℕ) : Fits w (x.mem addr) := by fits
example (x : Data 2) (hx : x.Bounded w) : Fits w (x.regs r0 &&& x.regs r1) := by fits
example (x : Data 2) (hx : x.Bounded w) (k : ℕ) : Fits w (x.regs r0 >>> k) := by fits

/-! `GenericRAM.Signed.Fits` compatibility, including cross-domain unsigned bounds. -/

example {z : ℤ} (h : Cslib.GenericRAM.Signed.Fits w z) :
    Cslib.GenericRAM.Signed.Fits (w + 1) z := by fits
example {z₁ z₂ : ℤ} (h₁ : Cslib.GenericRAM.Signed.Fits w z₁)
    (h₂ : Cslib.GenericRAM.Signed.Fits w z₂) :
    Cslib.GenericRAM.Signed.Fits (w + 1) (z₁ + z₂) := by fits
example {z : ℤ} (h : Cslib.GenericRAM.Signed.Fits w z) :
    Fits (w + 2) z.natAbs := by fits
example {z₁ z₂ : ℤ} (h₁ : Cslib.GenericRAM.Signed.Fits w z₁)
    (h₂ : Cslib.GenericRAM.Signed.Fits w z₂) :
    Fits (w + 2) (2 * (z₁.natAbs + z₂.natAbs) + 1) := by fits

/-! `ExactNotation` supports `d ← rand s`, and `ram_eval` handles `Fin.mk.injEq` & `reduceFits`. -/

example : (ram_exact[ r1 ← rand r0 ] : Code .exact 2) = .rand r1 r0 := rfl

example (x : Data 2) (hx : x.regs r0 = n) (hfit : Fits w n) (k : ℕ) (hk : x.regs r1 = k) :
    ExecWithin w ram[ r0 ← r0 >>> r1 ] x (x.set r0 (n >>> k)) 1 := by
  ram_eval [hx, hk]

example (x : Data 2) (hx : x.regs r0 = n) (hy : x.regs r1 = a) (hfit : Fits w n) :
    ExecWithin w ram[ r0 ← r0 &&& r1 ] x (x.set r0 (n &&& a)) 1 := by
  ram_eval [hx, hy]

example (x : Data 2) (hx : x.regs r0 = n) (hy : x.regs r1 = a) (hfit : Fits w n) :
    ExecWithin w ram[ r0 ← r0 / r1; r0 ← r0 % r1 ] x
      ((x.set r0 (n / a)).set r0 (n / a % a)) 2 := by
  ram_eval [hx, hy]

example {s : ℕ} (x : Data (s + 2)) (hx : x.regs ⟨0, by omega⟩ = n) (hfit : Fits w (n + 1)) :
    let z0 : Fin (s + 2) := ⟨0, by omega⟩
    let z1 : Fin (s + 2) := ⟨1, by omega⟩
    ExecWithin w ram[ z1 ← #1; z1 ← z0 + z1 ] x ((x.set z1 1).set z1 (n + 1)) 2 := by
  ram_eval [hx]

/-! Failures. -/

/-- error: fits: the goal is not a word-size bound `Fits w v` or `v < 2 ^ w`; use `omega` -/
#guard_msgs (substring := true) in
example (_h : Fits w a) (h : a ≤ b) : a ≤ b + 1 := by
  fits

/-- error: fits: `omega` could not prove the bound. Hypotheses that mention `Fits`: 1. -/
#guard_msgs (substring := true) in
example (_h : Fits w n) : Fits w (n + 1) := by
  fits

/-- error: fits: `omega` could not prove the bound. There is no hypothesis `Fits w v` in context. -/
#guard_msgs (substring := true) in
example : Fits w (n + 1) := by
  fits

end
