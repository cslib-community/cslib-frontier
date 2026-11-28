/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: local-only

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.SpecU2

/-! Tests of the sorting and neighbour-comparison layer (M1, part 2/3):
radix sort table/lookup neighbour check (`chk_table` holding and failing), shifted comparison
witness `XG` (`exists_cmpG`), and `IMU` tape-matching characterization (`imu_table`). -/

namespace CslibFrontierTests.TapeSort

open List.RadixSort
open Cslib.Circuits.Arithmetic.Separation.Uni

/-! ### Radix sort and neighbour check -/

/-- Every lookup key present in the table passes `chk none (srt …)` over `Bool`. -/
example :
    let T : List (Fin 2 → Bool) := [![false, true], ![true, false]]
    let L : List (Fin 2 → Bool) := [![true, false], ![false, true], ![true, false]]
    chk none (srt [false, true]
      (T.map (fun x => (false, x)) ++ L.map fun x => (true, x)) 2) := by
  have hbs : ∀ b : Bool, b ∈ [false, true] := fun b => by cases b <;> simp
  have hnd : ([false, true] : List Bool).Nodup := by decide
  rw [chk_table hbs hnd]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with rfl | rfl | rfl <;> simp

/-- A lookup key absent from the table fails `chk none (srt …)` (negative check). -/
example :
    ¬ chk none (srt [false, true]
      (([ ![false, false] ]).map (fun x => (false, x)) ++
        ([ ![true, true] ]).map fun x => (true, x)) 2) := by
  have hbs : ∀ b : Bool, b ∈ [false, true] := fun b => by cases b <;> simp
  have hnd : ([false, true] : List Bool).Nodup := by decide
  rw [chk_table hbs hnd]
  intro h
  have hmem : (![true, true] : Fin 2 → Bool) ∈ [ ![false, false] ] := h _ (by simp)
  simp only [List.mem_singleton] at hmem
  have h0 := congrFun hmem 0
  contradiction

/-! ### Shifted neighbour comparison (`XG`) -/

/-- A valid sorted list `[entry a, lookup a, entry b]` admits a comparison witness `XG`. -/
example :
    let l : List (Bool × ℕ) := [(false, 1), (true, 1), (false, 2)]
    ∃ y : XG ℕ, PlG y = l ∧ QlG y = l := by
  refine (exists_cmpG (by simp)).2 ?_
  simp [chkG]

/-- A non-empty list starting with a lookup fails `exists_cmpG` (negative check). -/
example :
    ¬ ∃ y : XG ℕ, PlG y = [(true, 0)] ∧ QlG y = [(true, 0)] := by
  rw [exists_cmpG (by simp)]
  simp [chkG]

/-! ### Full tape-matching sorting run (`IMU`) -/

/-- Positive `imu_table`: concrete lookup matching a table entry yields an `IMU` witness. -/
example :
    ∃ x : XU Unit Unit,
      IMU x (encW (recs 0
        (([(fun _ : Fin 1 => (.inl () : Bl Unit))]).map (fun k => (false, k)) ++
          ([(fun _ : Fin 1 => (.inl () : Bl Unit))]).map fun k => (true, k)))) :=
  (imu_table (M := Unit) [fun _ => .inl ()] [fun _ => .inl ()] (by simp)).2 fun _ hx => hx

/-- Negative `imu_table`: a lookup missing from the table admits no `IMU` witness. -/
example :
    ¬ ∃ x : XU Unit Unit,
      IMU x (encW (recs 0
        (([(fun _ : Fin 1 => (.inl () : Bl Unit))]).map (fun k => (false, k)) ++
          ([(fun _ : Fin 1 => (.inr (fun _ => false) : Bl Unit))]).map fun k => (true, k)))) := by
  rw [imu_table (M := Unit) _ _ (by simp)]
  intro h
  have hmem := h (fun _ => .inr (fun _ => false)) (by simp)
  have h0 := congrFun (List.mem_singleton.1 hmem) 0
  contradiction

end CslibFrontierTests.TapeSort
