/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Foundations.Combinatorics.SeededPackingRank.Balance

open Cslib Cslib.PacketPacking.Seeded

-- Empty graphs are balanced for every label width and every seed.
example {R C : Type*} (U a : ℕ) (v : R ⊕ C ↪ Fin U)
    (r : Fin 0 → R) (c : Fin 0 → C) (s : BalancedSchedules.SeededLabels.Seed U (6 * a)) :
    Balanced U a v r c s :=
  (balanced_iff_rank_succ_mul_le U a v r c s).2 fun e => Fin.elim0 e

-- A singleton with positive label width overloads its single occupied class for every seed.
example {R C : Type*} (U : ℕ) (v : R ⊕ C ↪ Fin U)
    (r : Fin 1 → R) (c : Fin 1 → C) (s : BalancedSchedules.SeededLabels.Seed U 6) :
    ¬ Balanced U 1 v r c s := by
  intro h
  have he := (balanced_iff_rank_succ_mul_le U 1 v r c s).1 h 0
  norm_num at he
  omega

-- A zero-bit verifier suffices for the unique rank of a singleton with empty labels.
example {R C : Type*} (U : ℕ) (v : R ⊕ C ↪ Fin U)
    (r : Fin 1 → R) (c : Fin 1 → C) (s : BalancedSchedules.SeededLabels.Seed U 0) :
    Balanced U 0 v r c s := by
  apply (balanced_iff_rank_bit_checks U 0 v r c s (width := 0) (by simp)
    (fun _ _ _ => False) (fun _ j => Fin.elim0 j)).2
  intro _
  exact ⟨0, by simp, fun j => Fin.elim0 j⟩
