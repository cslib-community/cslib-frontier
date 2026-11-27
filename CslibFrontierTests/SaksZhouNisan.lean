/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou
import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON
import Mathlib.Tactic.NormNum

/-! Boundary witnesses and non-vacuous instantiations for `walkStep`, `dens_foldl_walkStep_eq`,
`dens_snapIter_bitNisanPow_far_le`, and `exists_saksZhouSeeds_of_mem_BPL`. -/

namespace CslibFrontierTests.SaksZhouNisan

open Cslib Cslib.BitString Cslib.Complexity Cslib.Probability.SaksZhou

/-! ### `walkStep` boundaries and exact matrix-power realization -/

-- An absorbing sink `none` stays `none`, and the substochastic hypothesis `∑ j, A i j ≤ 1` in
-- `dens_walkStep_eq` is essential (`!![2]` has entry `2 > 1` while any density is `≤ 1`).
example (A : Matrix (Fin 1) (Fin 1) ℝ) (x : Bool) : walkStep A none x = none :=
  walkStep_none A x

example :
    (Finset.dens {x : Bool | walkStep (!![2] : Matrix (Fin 1) (Fin 1) ℝ) (some 0) x = some 0} :
      ℝ) ≠ (!![(2 : ℝ)] 0 0) := by
  have hle : (Finset.dens {x : Bool |
      walkStep (!![2] : Matrix (Fin 1) (Fin 1) ℝ) (some 0) x = some 0} : ℝ) ≤ 1 := by
    exact_mod_cast Finset.dens_le_one
  have h2 : (!![(2 : ℝ)] 0 0) = 2 := rfl
  linarith

-- Both single-step (`dens_walkStep_eq`) and 2-step (`dens_foldl_walkStep_eq`) walks realize powers
-- of `!![1/2, 1/2; 0, 1/2]` over `X = Bool` (`0 → 0` has weight `1/4`, `0 → 1` has weight `1/2`).
example :
    let toySub : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 0, 1 / 2]
    (Finset.dens {x : Bool | walkStep toySub (some 0) x = some 1} : ℝ) = 1 / 2 := by
  intro toySub
  have h0 : ∀ i j, 0 ≤ toySub i j := fun i j => by
    fin_cases i <;> fin_cases j <;> norm_num [toySub]
  have h1 : ∀ i, ∑ j, toySub i j ≤ 1 := fun i => by
    fin_cases i <;> norm_num [toySub, Fin.sum_univ_two]
  have hA : ∀ i j, ∃ c : ℕ, toySub i j * Fintype.card Bool = c := fun i j => by
    fin_cases i <;> fin_cases j <;> simp only [toySub, Fintype.card_bool, Nat.cast_ofNat]
    · exact ⟨1, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
  rw [dens_walkStep_eq h0 h1 hA 0 1]
  norm_num [toySub]

example :
    let toySub : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 0, 1 / 2]
    (Finset.dens {u : Fin 2 → Bool | (List.ofFn u).foldl (walkStep toySub) (some 0) = some 0} :
      ℝ) = 1 / 4 ∧
    (Finset.dens {u : Fin 2 → Bool | (List.ofFn u).foldl (walkStep toySub) (some 0) = some 1} :
      ℝ) = 1 / 2 := by
  intro toySub
  have h0 : ∀ i j, 0 ≤ toySub i j := fun i j => by
    fin_cases i <;> fin_cases j <;> norm_num [toySub]
  have h1 : ∀ i, ∑ j, toySub i j ≤ 1 := fun i => by
    fin_cases i <;> norm_num [toySub, Fin.sum_univ_two]
  have hA : ∀ i j, ∃ c : ℕ, toySub i j * Fintype.card Bool = c := fun i j => by
    fin_cases i <;> fin_cases j <;> simp only [toySub, Fintype.card_bool, Nat.cast_ofNat]
    · exact ⟨1, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
  constructor
  · rw [dens_foldl_walkStep_eq h0 h1 hA 2 0 0, sq, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num [toySub]
  · rw [dens_foldl_walkStep_eq h0 h1 hA 2 0 1, sq, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num [toySub]

/-! ### Non-vacuous `dens_snapIter_bitNisanPow_far_le` and `exists_saksZhouSeeds_of_mem_BPL` -/

-- With `d = 4`, `k = 1`, `n₂ = 1`, `m = 18` (`36`-bit blocks), `ε = 1 / 128`, the failure density
-- of `snapIter 4 (bitNisanPow 36 1 · hs) toySub 1 z` from `toySub ^ 2` is at most `97 / 128 < 1`.
example :
    let toySub : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 0, 1 / 2]
    ((rowFarSet ((2 : ℝ) ^ (1 * 1) * (Fintype.card (Fin 2) * (2 / 2 ^ 4)))
        (fun p : NisanShiftSeed (2 * 18) 1 1 4 =>
          snapIter 4 (fun A => bitNisanPow (2 * 18) 1 A p.1) toySub 1 p.2)
        (toySub ^ 2 ^ (1 * 1))).dens : ℝ) ≤ 97 / 128 := by
  intro toySub
  have h0 : ∀ i j, 0 ≤ toySub i j := fun i j => by
    fin_cases i <;> fin_cases j <;> norm_num [toySub]
  have h1 : ∀ i, ∑ j, toySub i j ≤ 1 := fun i => by
    fin_cases i <;> norm_num [toySub, Fin.sum_univ_two]
  have hM : ∀ i j, ∃ c : ℕ, toySub i j * Fintype.card (BitString (2 * 18)) = c := by
    intro i j
    have hcard : Fintype.card (BitString (2 * 18)) = 2 * 2 ^ 35 := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      decide
    rw [hcard]
    fin_cases i <;> fin_cases j <;> simp only [toySub, Matrix.of_apply, Nat.cast_mul,
      Nat.cast_ofNat]
    · exact ⟨1 * 2 ^ 35, by norm_num [Matrix.cons_val']⟩
    · exact ⟨1 * 2 ^ 35, by norm_num [Matrix.cons_val']⟩
    · exact ⟨0 * 2 ^ 35, by norm_num [Matrix.cons_val']⟩
    · exact ⟨1 * 2 ^ 35, by norm_num [Matrix.cons_val']⟩
  have herr : (Fintype.card (Fin 2) + 1 : ℝ) *
      ((2 ^ 1 - 1) * (Fintype.card (Fin 2) + 1) / 2 ^ 18) ≤ ((1 : ℝ) / 128) ^ 2 := by
    norm_num
  have h := dens_snapIter_bitNisanPow_far_le 4 18 1 1 le_rfl (by omega) h0 h1 hM (by norm_num) herr
  refine h.trans_eq ?_
  norm_num

-- The compact-ID estimate decides USTCON by a strict majority of the seeds.
example :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (M : Turing.MultiTapePTM k Bool State)
      (c clk : ℕ), ∀ a,
        ∃ hs : M.toNTM.RunsInSpace (encUSTCON a) (c * (Nat.log2 (encUSTCON a).length + 1)),
          let R := clk * (Nat.log2 (encUSTCON a).length + 2) + 1
          let s := Nat.sqrt R + 1
          let d := 5 * R + 5
          let m := 5 * d
          a ∈ USTCON ↔ (1 : ℝ) / 2 < (Finset.dens (Finset.univ.filter fun
            p : NisanShiftSeed (2 * m) s s d =>
            (1 : ℝ) / 2 < M.saksZhouAcceptEst c hs m s d p) : ℝ) := by
  obtain ⟨k, State, hfin, M, c, clk, h⟩ :=
    exists_saksZhouSeeds_of_mem_BPL (L_subset_BPL USTCON_mem_L)
  refine ⟨k, State, hfin, M, c, clk, fun a => ?_⟩
  obtain ⟨hs, _, _, _, hmem, hnot⟩ := h a
  exact ⟨hs, hmem, fun h₁ => by_contra fun h₂ => (hnot h₂).asymm h₁⟩

end CslibFrontierTests.SaksZhouNisan
