/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.PPoly.ReductionSize
import CslibFrontier.Computability.Circuit.Boolean.Hierarchy
import Mathlib.Tactic.FinCases

set_option linter.privateModule false

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

-- Wiring the input unchanged costs no gates and preserves the target's exact bound.
example {A : Language Bool} {s : ℕ → ℕ} (hA : A ∈ SIZE s) :
    A ∈ SIZE (fun n => 0 + s n) :=
  fixedWidth_size_of_reduction id (fun _ => 0) s (fun _ x => x)
    (fun n => by
      have h := complexity_wiring (I := interpretation) (id : Fin n → Fin n)
      simpa only [Function.comp_id, Nat.le_zero] using h)
    (fun _ _ => Iff.rfl) hA

-- The leading data bits are preserved independently of the trailing flags.
example : List.ofFn (readPaddedPrefix (m := 2) (1 : Fin 3) ![true, false, false, true, false]) =
    [true] := by decide
example : List.ofFn (readPaddedPrefix (m := 2) (0 : Fin 3) ![true, true, true, false, false]) =
    [] := by decide

-- A true leading bit selects one zero bit. A false or missing leading bit selects the empty word.
private def firstBit (n : ℕ) (x : Fin n → Bool) : Bool :=
  if h : 0 < n then x ⟨0, h⟩ else false

private def outputs (n : ℕ) (x : Fin n → Bool) : Fin (1 + (1 + 1)) → Bool :=
  Fin.append (fun _ : Fin 1 => false) ![!firstBit n x, firstBit n x]

example : outputs 1 ![false] (Fin.natAdd 1 0) = true := by decide
example : outputs 1 ![true] (Fin.natAdd 1 1) = true := by decide

private def Source : Language Bool := {w | w.headD false = true}

private def Target : Language Bool := {w | w.length = 1}

private theorem firstBit_size (n : ℕ) : complexity interpretation (single (firstBit n)) ≤ 1 := by
  cases n with
  | zero => exact (complexity_const false).le
  | succ n =>
    change complexity interpretation (single fun x : Fin (n + 1) → Bool => x 0) ≤ 1
    rw [complexity_single_proj]
    decide

private theorem outputs_size (n : ℕ) : complexity interpretation (outputs n) ≤ 6 := by
  have each (i : Fin 3) : complexity interpretation (single fun x => outputs n x i) ≤ 2 := by
    fin_cases i
    · change complexity interpretation (single fun _ : Fin n → Bool => false) ≤ 2
      simp [complexity_const]
    · change complexity interpretation (single fun x => !firstBit n x) ≤ 2
      exact (complexity_not_le _).trans (Nat.add_le_add_right (firstBit_size n) 1)
    · change complexity interpretation (single (firstBit n)) ≤ 2
      exact (firstBit_size n).trans (by decide)
  calc
    _ ≤ ∑ i : Fin 3, complexity interpretation (single fun x => outputs n x i) :=
      complexity_pi_le _
    _ ≤ ∑ _ : Fin 3, (2 : ℕ) := Finset.sum_le_sum fun i _ => each i
    _ = 6 := by simp

private theorem correct (n : ℕ) (x : Fin n → Bool) : ∃ i : Fin (1 + 1),
    (∀ j, outputs n x (Fin.natAdd 1 j) = true ↔ j = i) ∧
      (List.ofFn x ∈ Source ↔ List.ofFn (readPaddedPrefix i (outputs n x)) ∈ Target) := by
  have head : (List.ofFn x).headD false = firstBit n x := by
    cases n with
    | zero => simp [firstBit]
    | succ n => simp [firstBit, List.ofFn_succ]
  cases h : firstBit n x
  · refine ⟨0, fun j => ?_, ?_⟩
    · simp only [outputs, Fin.append_right, h]
      fin_cases j <;> decide
    · change (List.ofFn x).headD false = true ↔
        (List.ofFn (readPaddedPrefix (m := 1) 0 (outputs n x))).length = 1
      rw [head, h, List.length_ofFn]
      decide
  · refine ⟨1, fun j => ?_, ?_⟩
    · simp only [outputs, Fin.append_right, h]
      fin_cases j <;> decide
    · change (List.ofFn x).headD false = true ↔
        (List.ofFn (readPaddedPrefix (m := 1) 1 (outputs n x))).length = 1
      rw [head, h, List.length_ofFn]
      decide

private theorem target_size : Target ∈ SIZE (fun _ => 1) := by
  intro n
  have eq : Target.slice n = fun _ => decide (n = 1) := by
    funext x
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
    change (List.ofFn x).length = 1 ↔ (decide (n = 1) : Bool) = true
    simp only [List.length_ofFn, decide_eq_true_eq]
  change complexity interpretation (single (Target.slice n)) ≤ 1
  rw [eq, complexity_const]

private theorem degrees : CircuitReductionDegrees Source Target 0 0 :=
  ⟨6, 2, fun _ => 1, outputs, fun n => by simpa using outputs_size n, by simp, correct⟩

example : Source ∈ SIZE (fun _ => 13) :=
  variableWidth_size_of_reduction (fun _ => 1) (fun _ => 6) (fun _ => 1) (fun _ => 1)
    outputs outputs_size (fun _ _ _ => le_rfl) correct target_size

example : ∃ K, Source ∈ SIZE (fun _ => K) := by
  simpa using size_of_reductionDegrees (d := 0) (C := 1) degrees (by simpa using target_size)

example : Target ∈ SIZE (fun n => (0 + 1 * 1 ^ 0) * (n + 1) ^ max 0 (1 * 0)) :=
  size_of_fixedWidth_degrees (A := Target) (B := Target) (a := 0) (b := 1) (d := 0) (C := 1)
    (R := 0) (M := 1) id (fun _ x => x)
    (fun n => by
      have h := complexity_wiring (I := interpretation) (id : Fin n → Fin n)
      simpa using h)
    (by simp) (fun _ _ => Iff.rfl) (by simpa using target_size)

example {A B : Language Bool}
    (hard : ∀ c, A ∉ SIZE (fun n => c * (n + 1) ^ 2))
    (red : CircuitReductionDegrees A B 1 1)
    (upper : B ∈ SIZE (fun n => 1 * (n + 1) ^ 3)) :
    2 < max 1 (1 * (3 + 1)) :=
  reduction_degree_tradeoff hard red upper

example {B : Language Bool}
    (family : ∀ k, ∃ A : Language Bool,
      (∀ c, A ∉ SIZE (fun n => c * (n + 1) ^ k)) ∧ CircuitReductionDegrees A B 1 1) :
    B ∉ PPoly :=
  outside_PPoly_of_common_circuitReductionDegrees family
