/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Program
public import Cslib.Computability.Circuit.Signature
import CslibFrontier.Computability.Circuit.StraightLine
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Straight-line programs as lists of steps

A straight-line program over `Fin D` is a cslib `Program` over `fullSignature 2 (Fin D)`, which has
one constant symbol for every element of `Fin D` and one binary symbol for every operation on
`Fin D`, with `fullInterpretation`. The source *VP ≠ VNP over every field* [AnthropicVPVNP2026]
(module `Nc.Cut.Slp`, `IsSlpStep`) describes such programs instead as lists of functions, each of
which is an input, a constant, or a binary operation of two earlier ones.

The two descriptions agree up to the inputs: a list of `p` such steps is computed by a program
with `p` gates (`Cslib.Circuits.exists_program_of_isSlpStep`), and a program with `p` gates on
`n` inputs gives a list of `n + p` steps (`Cslib.Circuits.exists_isSlpStep_of_program`).

## Main definitions

* `Cslib.Circuits.IsSlpStep`: one step of a straight-line program given as a list of functions.

## Main results

* `Cslib.Circuits.exists_program_of_isSlpStep`, `Cslib.Circuits.exists_isSlpStep_of_program`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Nc.Cut.Slp`
-/

public section

namespace Cslib.Circuits

variable {D : ℕ}

variable {Inp : Type} {n : ℕ}

/-- Step `k` of the list `fn`: an input coordinate, a constant, or a binary operation of two earlier
steps. -/
@[expose] def IsSlpStep (inp : Fin n → Inp → Fin D) (fn : ℕ → Inp → Fin D) (k : ℕ) : Prop :=
  (∃ i, fn k = inp i) ∨ (∃ c, fn k = fun _ => c) ∨
    ∃ i < k, ∃ j < k, ∃ φ : Fin D → Fin D → Fin D, ∀ x, fn k x = φ (fn i x) (fn j x)

/-- A list of `p` steps is computed by a program with `p` gates, gate `k` computing step `k`. -/
theorem exists_program_of_isSlpStep (inp : Fin n → Inp → Fin D) (fn : ℕ → Inp → Fin D) {p : ℕ}
    (h : ∀ k < p, IsSlpStep inp fn k) :
    ∃ P : Program (fullSignature 2 (Fin D)) n p,
      ∀ (k : Fin p) x, P.eval fullInterpretation (fun i => inp i x) k = fn k x := by
  have step : ∀ j : Fin p, ∃ line : Line (fullSignature 2 (Fin D)) n j, ∀ x,
      fn j x = line.eval fullInterpretation (fun i => inp i x) fun t => fn t x := by
    intro j
    rcases h j j.isLt with ⟨i, hi⟩ | ⟨c, hc⟩ | ⟨i, hi, k, hk, φ, hφ⟩
    · exact ⟨⟨.fn fun a => a 0, (![Wire.input i, Wire.input i] : Fin 2 → Wire n j)⟩,
        fun x => by rw [hi]; rfl⟩
    · exact ⟨⟨.con c, Fin.elim0⟩, fun x => by rw [hc]; rfl⟩
    · exact ⟨⟨.fn fun a => φ (a 0) (a 1),
        (![Wire.gate ⟨i, hi⟩, Wire.gate ⟨k, hk⟩] : Fin 2 → Wire n j)⟩, fun x => by rw [hφ]; rfl⟩
  choose line hline using step
  obtain ⟨P, hP, -⟩ := Program.exists_eval_eq_of_prefixLines fullInterpretation
    (fun x i => inp i x) line (fun x j => fn j x) fun x j => hline j x
  exact ⟨P, fun k x => congrFun (hP x) k⟩

/-- A program with `p` gates on `n` inputs gives a list of `n + p` steps: first the inputs, then
the gates. -/
theorem exists_isSlpStep_of_program [NeZero D] (inp : Fin n → Inp → Fin D) {p : ℕ}
    (P : Program (fullSignature 2 (Fin D)) n p) :
    ∃ fn : ℕ → Inp → Fin D, (∀ k < n + p, IsSlpStep inp fn k) ∧
      (∀ i : Fin n, fn i = inp i) ∧
      ∀ (k : Fin p) x, fn (n + k) x = P.eval fullInterpretation (fun i => inp i x) k := by
  classical
  induction P with
  | empty =>
    refine ⟨fun m x => if h : m < n then inp ⟨m, h⟩ x else 0, fun k hk => ?_, fun i => ?_,
      fun k => k.elim0⟩
    · exact Or.inl ⟨⟨k, by omega⟩, funext fun x => by simp [show k < n by omega]⟩
    · funext x
      simp
  | @gate g P line ih =>
    obtain ⟨fn, hs, hin, hg⟩ := ih
    let I : Interpretation (fullSignature 2 (Fin D)) (Fin D) := fullInterpretation
    let new : Inp → Fin D := fun x => line.eval I (fun i => inp i x) (P.eval I fun i => inp i x)
    -- the step index of a wire, and its value
    let idx : Wire n g → ℕ := fun w => Wire.elim (fun i => (i : ℕ)) (fun j => n + j) w
    have hidx : ∀ w, idx w < n + g := fun w => by cases w <;> simp [idx, Wire.elim]; omega
    have hval : ∀ w x, fn (idx w) x = Wire.elim (fun i => inp i x) (P.eval I fun i => inp i x) w :=
      fun w x => by
        cases w with
        | input i => simp [idx, Wire.elim, hin i]
        | gate j => simp [idx, Wire.elim, hg j x, I]
    have hne : ∀ m < n + g, Function.update fn (n + g) new m = fn m := fun m hm =>
      Function.update_of_ne (by omega) _ _
    refine ⟨Function.update fn (n + g) new, fun k hk => ?_, fun i => ?_, fun k x => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (show k < n + g + 1 by omega) with hk | rfl
      · rcases hs k hk with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, φ, h1⟩
        · exact Or.inl ⟨i, by rw [hne k hk, h1]⟩
        · exact Or.inr (Or.inl ⟨c, by rw [hne k hk, h1]⟩)
        · refine Or.inr (Or.inr ⟨i, hi, j, hj, φ, fun x => ?_⟩)
          rw [hne k hk, hne i (by omega), hne j (by omega), h1]
      · rw [IsSlpStep, Function.update_self]
        obtain ⟨op, wires⟩ := line
        cases op with
        | con c => exact Or.inr (Or.inl ⟨c, funext fun x => rfl⟩)
        | fn f =>
          let w : Fin 2 → Wire n g := wires
          refine Or.inr (Or.inr ⟨idx (w 0), hidx _, idx (w 1), hidx _,
            fun a b => f ![a, b], fun x => ?_⟩)
          rw [hne _ (hidx _), hne _ (hidx _), hval, hval]
          change f _ = f _
          congr 1
          funext i
          fin_cases i <;> rfl
    · funext x
      rw [hne i (by omega), hin i]
    · induction k using Fin.lastCases with
      | last =>
        rw [Program.eval_gate_last, Fin.val_last, Function.update_self]
      | cast k =>
        rw [Program.eval_gate_castSucc, Fin.val_castSucc, hne _ (by omega), hg k x]

end Cslib.Circuits
