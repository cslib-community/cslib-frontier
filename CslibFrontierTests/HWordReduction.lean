/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteReduction

/-! Standard reduction and total-input boundary cases, including an empty source alphabet. -/

open Cslib.Complexity.NCL HWord.RewriteGadget

private def emptyRules : Fin 0 → Rule 0 := Fin.elim0

example : toHWord (r := 0) (HWord.Instance.mk [] []) ∈
    HWord.language (compatibility emptyRules) :=
  (toHWord_mem_iff emptyRules _).mpr .refl

private def singletonRules : Fin 0 → Rule 1 := Fin.elim0

example : toHWord (r := 0) (HWord.Instance.mk [] [0]) ∉
    HWord.language (compatibility singletonRules) := by
  intro h
  have hlen := source_path_length singletonRules ((toHWord_mem_iff singletonRules _).mp h)
  simp at hlen

private def forward : Digraph (Fin 2) := ⟨fun a b => a = 0 ∧ b = 1⟩

private instance : DecidableRel forward.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

example : HWord.Legal forward (id : Fin 2 → Fin 2) := by decide +kernel

-- Reflexive reachability still checks the initial word's directed compatibility.
example : HWord.Instance.mk
    (List.ofFn (fun i : Fin 2 => (1 : Fin 2) - i))
    (List.ofFn (fun i : Fin 2 => (1 : Fin 2) - i)) ∉ HWord.language forward := by
  rw [HWord.language_ofFn]
  rintro ⟨h, _⟩
  exact (by decide +kernel : ¬HWord.Legal forward (fun i : Fin 2 => (1 : Fin 2) - i)) h
