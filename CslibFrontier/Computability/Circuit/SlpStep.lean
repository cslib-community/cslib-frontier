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
`n` inputs gives a list of `n + p` steps (`Cslib.Circuits.exists_isSlpStep_of_program`). Steps stay
steps when the inputs are read through a map (`Cslib.Circuits.IsSlpStep.comp`).

## Main definitions

* `Cslib.Circuits.IsSlpStep`: one step of a straight-line program given as a list of functions.

## Main results

* `Cslib.Circuits.exists_program_of_isSlpStep`, `Cslib.Circuits.exists_isSlpStep_of_program`.
* `Cslib.Circuits.IsSlpStep.comp`: steps of functions of a map of the inputs.

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

/-- A step of the list `fn` is a step of the functions `fn k ∘ f`, from the inputs `inp i ∘ f`. -/
theorem IsSlpStep.comp {Inp' : Type} {inp : Fin n → Inp → Fin D} {fn : ℕ → Inp → Fin D} {k : ℕ}
    (f : Inp' → Inp) (h : IsSlpStep inp fn k) :
    IsSlpStep (fun i x => inp i (f x)) (fun k x => fn k (f x)) k := by
  rcases h with ⟨i, hi⟩ | ⟨c, hc⟩ | ⟨i, hi, j, hj, φ, hφ⟩
  exacts [.inl ⟨i, funext fun x => congrFun hi (f x)⟩,
    .inr (.inl ⟨c, funext fun x => congrFun hc (f x)⟩),
    .inr (.inr ⟨i, hi, j, hj, φ, fun x => hφ (f x)⟩)]

/-- A list of `p` steps is computed by a program with `p` gates, gate `k` computing step `k`. -/
theorem exists_program_of_isSlpStep (inp : Fin n → Inp → Fin D) (fn : ℕ → Inp → Fin D) {p : ℕ}
    (h : ∀ k < p, IsSlpStep inp fn k) :
    ∃ P : Program (fullSignature 2 (Fin D)) n p,
      ∀ (k : Fin p) x, P.eval fullInterpretation (fun i => inp i x) k = fn k x := by
  choose line hline using fun j : Fin p => show ∃ line : Line (fullSignature 2 (Fin D)) n j,
      ∀ x, fn j x = line.eval fullInterpretation (fun i => inp i x) fun t => fn t x by
    rcases h j j.isLt with ⟨i, hi⟩ | ⟨c, hc⟩ | ⟨i, hi, k, hk, φ, hφ⟩
    · exact ⟨⟨.fn (· 0), ![.input i, .input i]⟩, fun x => by rw [hi]; rfl⟩
    · exact ⟨⟨.con c, Fin.elim0⟩, fun x => by rw [hc]; rfl⟩
    · exact ⟨⟨.fn fun a => φ (a 0) (a 1), ![.gate ⟨i, hi⟩, .gate ⟨k, hk⟩]⟩,
        fun x => by rw [hφ]; rfl⟩
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
    exact ⟨fun m x => if h : m < n then inp ⟨m, h⟩ x else 0,
      fun k hk => .inl ⟨⟨k, by omega⟩, funext fun x => by simp [show k < n by omega]⟩,
      fun _ => funext fun _ => by simp, fun k => k.elim0⟩
  | @gate g P line ih =>
    obtain ⟨fn, hs, hin, hg⟩ := ih
    let I : Interpretation (fullSignature 2 (Fin D)) (Fin D) := fullInterpretation
    let new : Inp → Fin D := fun x => line.eval I (inp · x) (P.eval I (inp · x))
    -- the step index of a wire, and its value
    let idx : Wire n g → ℕ := Wire.elim (fun i => i) (n + ·)
    have hidx (w) : idx w < n + g := by
      cases w <;> simp only [idx, Wire.elim] <;> omega
    have hval (w x) : fn (idx w) x = Wire.elim (inp · x) (P.eval I (inp · x)) w := by
      cases w with
      | input i => simp [idx, Wire.elim, hin i]
      | gate j => simp [idx, Wire.elim, hg j x, I]
    have hne (m) (hm : m < n + g) : Function.update fn (n + g) new m = fn m :=
      Function.update_of_ne (by omega) _ _
    refine ⟨Function.update fn (n + g) new, fun k hk => ?_,
      fun i => funext fun x => by rw [hne i (by omega), hin i], fun k x => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (show k < n + g + 1 by omega) with hk | rfl
      · rcases hs k hk with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, φ, h1⟩
        · exact .inl ⟨i, by rw [hne k hk, h1]⟩
        · exact .inr (.inl ⟨c, by rw [hne k hk, h1]⟩)
        · exact .inr (.inr ⟨i, hi, j, hj, φ, fun x => by
            rw [hne k hk, hne i (by omega), hne j (by omega), h1]⟩)
      · rw [IsSlpStep, Function.update_self]
        rcases line with ⟨op, w⟩
        cases op with
        | con c => exact .inr (.inl ⟨c, funext fun _ => rfl⟩)
        | fn f =>
          refine .inr (.inr ⟨idx (w (0 : Fin 2)), hidx _, idx (w (1 : Fin 2)), hidx _,
            (f ![·, ·]), fun x => ?_⟩)
          rw [hne _ (hidx _), hne _ (hidx _), hval, hval]
          exact congrArg f (funext fun i => by fin_cases i <;> rfl)
    · induction k using Fin.lastCases with
      | last =>
        rw [Program.eval_gate_last, Fin.val_last, Function.update_self]
      | cast k =>
        rw [Program.eval_gate_castSucc, Fin.val_castSucc, hne _ (by omega), hg k x]

end Cslib.Circuits
