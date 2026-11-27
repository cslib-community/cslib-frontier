/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Recursion.StackScheme
import CslibFrontier.Probability.BitString.UniformSplit
import CslibFrontier.Probability.PMF.Map
import Mathlib.Tactic.NormNum

/-!
# Module client tests for `StackScheme` and `UniformSplit`

Exercises both public interfaces under `module` encapsulation with ordinary `import`s and no
machine-model dependencies:

1. `Cslib.Algorithms.StackRecursion`: asymmetric Fibonacci recursion tree evaluated on an explicit
   stack in `2 * fibNodes n - 1` steps, checking `Eval`, `Loop.child`, `Eval.run`,
   `Eval.good_iterate`, `Scheme.run_eq_some`, and concrete `17`-step vs `16`-step traces at `n = 4`.
2. `Cslib.BitString` (`UniformSplit`): `uniformList_map_split`, `uniformList_drop`,
   `uniformList_map_split3`, and `uniformList_map_listRows` on concrete heterogeneous widths
   (including zero-width segments, composed 4-segment splits, and infinite codomain `ℕ`) together
   with exact point-mass checks.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CoinTapeStackScheme

section StackScheme

open Cslib.Algorithms.StackRecursion

/-- Fibonacci numbers, defined locally without machine or number-theory imports. -/
private def fibVal : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibVal (n + 1) + fibVal n

/-- Total nodes in the asymmetric recursion tree of `fibVal n`. -/
private def fibNodes : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => fibNodes (n + 1) + fibNodes n + 1

/-- Maximum number of open stack frames while evaluating `fibVal n`. -/
private def fibHeight : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => fibHeight (n + 1) + 1

/-- Explicit-stack scheme for `fibVal`: internal calls branch asymmetrically to `x - 1` then
`x - 2`, accumulating `(childrenDone, partialSum)`. -/
private def fibScheme : Scheme ℕ (ℕ × ℕ) ℕ where
  isLeaf x := decide (x < 2)
  leaf x := x
  start _ := (0, 0)
  next x a :=
    match a.1 with
    | 0 => some (x - 1)
    | 1 => some (x - 2)
    | _ => none
  absorb _ a y := (a.1 + 1, a.2 + y)
  finish _ a := a.2

private theorem fibVal_mono : Monotone fibVal := by
  have hstep : ∀ k, fibVal k ≤ fibVal (k + 1) ∧ fibVal (k + 1) ≤ fibVal (k + 2) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      simp only [fibVal]
      omega
  exact monotone_nat_of_le_succ fun k => (hstep k).1

private theorem fibHeight_mono : Monotone fibHeight := by
  refine monotone_nat_of_le_succ fun k => ?_
  rcases k with _ | _ | k <;> simp [fibHeight]

/-- Boundedness invariant along a run below root `n₀`. -/
private def fibInv (n₀ : ℕ) : Invariant ℕ (ℕ × ℕ) ℕ where
  node x := x ≤ n₀
  frame x a := x ≤ n₀ ∧ a.1 < 2 ∧ a.2 ≤ fibVal n₀
  value y := y ≤ fibVal n₀

/-- Every input `n ≤ n₀` has an explicit-stack derivation of `fibVal n` with `fibNodes n` nodes and
stack depth `fibHeight n`. -/
theorem eval_fibScheme {n₀ n : ℕ} (hn : n ≤ n₀) :
    fibScheme.Eval (fibInv n₀) n (fibVal n) (fibNodes n) (fibHeight n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · exact Scheme.Eval.leaf hn rfl (Nat.zero_le _)
    · exact Scheme.Eval.leaf hn rfl (show 1 ≤ fibVal n₀ by simpa [fibVal] using fibVal_mono hn)
    · have hc₁ := ih (k + 1) (by omega) (by omega)
      have hc₂ := ih k (by omega) (by omega)
      have hval : fibVal (k + 2) ≤ fibVal n₀ := fibVal_mono hn
      have hf₀ : (fibInv n₀).frame (k + 2) (0, 0) := ⟨hn, by omega, Nat.zero_le _⟩
      have hf₁ : (fibInv n₀).frame (k + 2) (1, 0 + fibVal (k + 1)) := by
        refine ⟨hn, by omega, ?_⟩
        simp only [fibVal] at hval
        omega
      have hloop : fibScheme.Loop (fibInv n₀) (k + 2) (0, 0)
          (2, 0 + fibVal (k + 1) + fibVal k) (fibNodes (k + 1) + (fibNodes k + 0))
          (max (fibHeight (k + 1)) (max (fibHeight k) 0)) :=
        Scheme.Loop.child hf₀ rfl hc₁
          (Scheme.Loop.child hf₁ rfl hc₂ (Scheme.Loop.done rfl))
      have heval := Scheme.Eval.call (R := fibScheme) (I := fibInv n₀) hn rfl hloop
        (show 0 + fibVal (k + 1) + fibVal k ≤ fibVal n₀ by
          simpa only [fibVal, Nat.zero_add] using hval)
      have hmax : max (fibHeight (k + 1)) (max (fibHeight k) 0) + 1 = fibHeight (k + 2) := by
        have hle : fibHeight k ≤ fibHeight (k + 1) := fibHeight_mono (Nat.le_succ k)
        simp only [fibHeight, Nat.max_zero]
        rw [max_eq_left hle]
      simpa only [fibScheme, fibVal, fibNodes, Nat.zero_add, Nat.add_zero, hmax] using heval

/-- Exact `2 * fibNodes n - 1`-step evaluation of `fibScheme` without any machine model. -/
example (n : ℕ) :
    fibScheme.step^[2 * fibNodes n - 1] ([], some n, none) = ([], none, some (fibVal n)) :=
  (eval_fibScheme le_rfl).run []

/-- Every state visited at any step `j` keeps at most `fibHeight n` open stack frames and
satisfies `fibInv n`. -/
example (n j : ℕ) :
    Scheme.Good (fibInv n) (fibHeight n) (fibScheme.step^[j] ([], some n, none)) :=
  (eval_fibScheme le_rfl).good_iterate j

/-- Sufficient fuel returns `some (fibVal n)` through `Scheme.run`. -/
example (n fuel : ℕ) (hfuel : 2 * fibNodes n - 1 ≤ fuel) :
    fibScheme.run (fun _ : Unit => fuel) (fun _ => n) () = some (fibVal n) :=
  Scheme.run_eq_some (eval_fibScheme le_rfl) hfuel

-- Concrete trace at `n = 4`: `fibVal 4 = 3` and `fibNodes 4 = 9`, so `2 * 9 - 1 = 17` steps finish,
-- while after `16` steps the root frame `(4, ...)` is still open on the stack.
example : fibNodes 4 = 9 ∧ fibScheme.run (fun _ : Unit => 17) (fun _ => 4) () = some 3 := by decide

example : (fibScheme.step^[16] ([], some 4, none)).1.length = 1 := by decide

end StackScheme

section UniformSplit

open Cslib.BitString Cslib.Probability
open scoped ENNReal

-- Two-segment `uniformList_map_split` on widths `2` and `3`.
example :
    (uniformList (2 + 3)).map (fun tape => (tape.take 2, tape.drop 2)) =
      (uniformList 2).bind fun s₁ => (uniformList 3).map fun s₂ => (s₁, s₂) :=
  uniformList_map_split 2 3 Prod.mk

-- Suffix projection `uniformList_drop`: dropping 2 bits from 5 fair bits gives `uniformList 3`,
-- assigning mass `1 / 8` to `[true, false, true]`.
example :
    ((uniformList (2 + 3)).map (List.drop 2)) [true, false, true] = (1 : ℝ≥0∞) / 8 := by
  rw [uniformList_drop 2 3, ← PMF.map_id (uniformList 3),
    uniformList_map_apply id 3 [true, false, true]]
  have hcard :
      (Finset.univ.filter fun r : Fin 3 → Bool => List.ofFn r = [true, false, true]).card = 1 := by
    decide
  simp only [id_eq, hcard, Nat.cast_one]
  norm_num

-- Three-segment `uniformList_map_split3` on heterogeneous widths `(1, 2, 3)` and degenerate middle
-- width `(2, 0, 3)`.
example :
    (uniformList (1 + (2 + 3))).map
        (fun tape =>
          (tape.take 1, (tape.drop 1).take 2, (tape.drop 1).drop 2)) =
      (uniformList 1).bind fun s₁ =>
        (uniformList 2).bind fun s₂ => (uniformList 3).map fun s₃ => (s₁, s₂, s₃) :=
  uniformList_map_split3 1 2 3 fun s₁ s₂ s₃ => (s₁, s₂, s₃)

example :
    (uniformList (2 + (0 + 3))).map
        (fun tape => (tape.take 2) ++ ((tape.drop 2).take 0) ++ ((tape.drop 2).drop 0)) =
      uniformList (2 + 3) := by
  rw [uniformList_map_split3 2 0 3 fun s₁ s₂ s₃ => s₁ ++ s₂ ++ s₃]
  simpa only [uniformList_zero, PMF.pure_bind, List.append_nil] using (uniformList_add 2 3).symm

-- Four-segment split on heterogeneous widths `(2, 1, 3, 2)` (`8` bits total) by composing
-- `uniformList_map_split` with `uniformList_map_split3`.
example :
    (uniformList (2 + (1 + (3 + 2)))).map
        (fun tape =>
          ((tape.take 2).count true,
            ((tape.drop 2).take 1).headD false,
            (((tape.drop 2).drop 1).take 3).count false,
            (((tape.drop 2).drop 1).drop 3).reverse)) =
      (uniformList 2).bind fun s₁ =>
        (uniformList 1).bind fun s₂ =>
          (uniformList 3).bind fun s₃ =>
            (uniformList 2).map fun s₄ =>
              (s₁.count true, s₂.headD false, s₃.count false, s₄.reverse) := by
  rw [uniformList_map_split 2 (1 + (3 + 2)) fun s₁ rest =>
    (s₁.count true, (rest.take 1).headD false,
      ((rest.drop 1).take 3).count false, ((rest.drop 1).drop 3).reverse)]
  congr 1 with s₁ : 1
  exact uniformList_map_split3 1 3 2 fun s₂ s₃ s₄ =>
    (s₁.count true, s₂.headD false, s₃.count false, s₄.reverse)

-- Block-row `uniformList_map_listRows` on `count = 3, width = 2` (`6` bits) into the infinite
-- codomain `ℕ`, checked both as an exact `PMF (List ℕ)` equality and at outcome `[2, 1, 0]`
-- (`(1 / 4) * (2 / 4) * (1 / 4) = 1 / 32`).
example :
    (uniformList (3 * 2)).map (fun w => (listRows 3 2 w).map (List.count true)) =
      (PMF.iid ((uniformList 2).map (List.count true)) 3).map List.ofFn :=
  uniformList_map_listRows 3 2 (List.count true)

example :
    ((uniformList (3 * 2)).map (fun w => (listRows 3 2 w).map (List.count true))) [2, 1, 0] =
      (1 : ℝ≥0∞) / 32 := by
  have hvec : List.ofFn ![2, 1, 0] = [2, 1, 0] := rfl
  rw [uniformList_map_listRows 3 2 (List.count true), ← hvec,
    PMF.map_apply_of_injective _ List.ofFn_injective, PMF.iid_apply, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, uniformList_map_apply]
  have hc2 : (Finset.univ.filter fun r : Fin 2 → Bool => (List.ofFn r).count true = 2).card = 1 :=
    by decide
  have hc1 : (Finset.univ.filter fun r : Fin 2 → Bool => (List.ofFn r).count true = 1).card = 2 :=
    by decide
  have hc0 : (Finset.univ.filter fun r : Fin 2 → Bool => (List.ofFn r).count true = 0).card = 1 :=
    by decide
  simp only [hc2, hc1, hc0, Nat.cast_one, Nat.cast_ofNat]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_one]
  norm_num

end UniformSplit

end CslibFrontierTests.CoinTapeStackScheme
