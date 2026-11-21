/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SparseModeLength
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Algebra.BigOperators.Fin

/-!
# Compressing rectangular exponent arrays

The sparse constructor drops zero entries and empty colours. Projection recovers every
original coordinate, and the sparse mass equals the sum of all positive weights times
their exponents.
-/

public section

namespace Cslib.SparseModeTuple

open Finset

/-- Compress a dense row after skipping the given number of initial zero weights. -/
@[expose] def packEntries (skip : ℕ) : List ℕ → List Entry
  | [] => []
  | 0 :: xs => packEntries (skip + 1) xs
  | (x + 1) :: xs => ⟨skip, x⟩ :: packEntries 0 xs

private theorem entryAt_packEntries (xs : List ℕ) (skip i : ℕ) :
    entryAt (packEntries skip xs) i = if i < skip then 0 else xs.getD (i - skip) 0 := by
  induction xs generalizing skip i with
  | nil => simp [packEntries, entryAt]
  | cons x xs ih =>
    cases x with
    | zero =>
      simp only [packEntries, ih]
      by_cases h : i < skip + 1
      · by_cases h' : i < skip <;> simp [h, h', show i - skip = 0 by omega]
      · have hs : i - skip = (i - (skip + 1)) + 1 := by omega
        simp [h, show ¬i < skip by omega, hs]
    | succ x =>
      simp only [packEntries, entryAt, ih, Nat.not_lt_zero, ite_false, Nat.sub_zero]
      by_cases h : i < skip
      · simp [h]
      · by_cases h' : i = skip
        · simp [h']
        · have hs : i - skip = (i - (skip + 1)) + 1 := by omega
          simp [h, h', hs]

/-- Compress the rows after skipping the given number of initial empty colours. -/
@[expose] def packRows (skip : ℕ) : List (List ℕ) → List Row
  | [] => []
  | xs :: xss =>
    match packEntries 0 xs with
    | [] => packRows (skip + 1) xss
    | e :: es => ⟨skip, e, es⟩ :: packRows 0 xss

private theorem coord_packRows (xss : List (List ℕ)) (skip c i : ℕ) :
    coord (packRows skip xss) c i =
      if c < skip then 0 else ((xss.getD (c - skip) []).getD i 0) := by
  induction xss generalizing skip c with
  | nil => simp [packRows, coord]
  | cons xs xss ih =>
    simp only [packRows]
    split
    next he =>
      rw [ih]
      have hzero : xs.getD i 0 = 0 := by simpa [he, entryAt] using (entryAt_packEntries xs 0 i).symm
      by_cases h : c < skip + 1
      · by_cases h' : c < skip
        · simp [h, h']
        · simp only [h, ite_true, h', ite_false, show c - skip = 0 by omega, List.getD_cons_zero,
            hzero]
      · have hs : c - skip = (c - (skip + 1)) + 1 := by omega
        simp [h, show ¬c < skip by omega, hs]
    next e es he =>
      have hh : entryAt (e :: es) i = xs.getD i 0 := by simpa [he] using entryAt_packEntries xs 0 i
      simp only [coord, ih, Nat.not_lt_zero, ite_false, Nat.sub_zero, hh]
      by_cases h : c < skip
      · simp [h]
      · by_cases h' : c = skip
        · simp [h']
        · have hs : c - skip = (c - (skip + 1)) + 1 := by omega
          simp [h, h', hs]

private theorem entryMass_packEntries (xs : List ℕ) (skip offset : ℕ) :
    entryMass offset (packEntries skip xs) = rankMass (offset + skip) xs := by
  induction xs generalizing skip offset with
  | nil => simp [packEntries, entryMass, rankMass]
  | cons x xs ih =>
    cases x <;> simp [packEntries, rankMass, entryMass, ih, Nat.add_assoc]

private theorem mass_packRows (xss : List (List ℕ)) (skip : ℕ) :
    mass (packRows skip xss) = (xss.map (rankMass 0)).sum := by
  induction xss generalizing skip with
  | nil => rfl
  | cons xs xss ih =>
    have hh := entryMass_packEntries xs 0 0
    simp only [packRows, List.map_cons, List.sum_cons]
    split
    next he =>
      have hm : rankMass 0 xs = 0 := by simpa [he, entryMass] using hh.symm
      simp [ih, hm]
    next e es he =>
      change entryMass 0 (e :: es) + mass (packRows 0 xss) = _
      have hm : entryMass 0 (e :: es) = rankMass 0 xs := by simpa [he] using hh
      rw [hm, ih]

private theorem colours_packRows_le (xss : List (List ℕ)) (skip : ℕ) :
    colours (packRows skip xss) ≤ skip + xss.length := by
  induction xss generalizing skip with
  | nil => simp [packRows, colours]
  | cons xs xss ih =>
    simp only [packRows, List.length_cons]
    split
    · have := ih (skip + 1)
      omega
    · change skip + 1 + colours (packRows 0 xss) ≤ _
      have := ih 0
      omega

/-- Compress a finite array indexed by a colour and a positive weight minus one. -/
@[expose] def ofFn {m n : ℕ} (β : Fin m → Fin n → ℕ) : List Row :=
  packRows 0 (List.ofFn fun c => List.ofFn (β c))

/-- Lookup in the sparse encoding recovers the exact finite exponent. -/
theorem coord_ofFn {m n : ℕ} (β : Fin m → Fin n → ℕ) (c : Fin m) (i : Fin n) :
    coord (ofFn β) c.val i.val = β c i := by simp [ofFn, coord_packRows]

/-- Reading outside the original rectangle gives zero. -/
theorem coord_ofFn_eq_zero {m n : ℕ} (β : Fin m → Fin n → ℕ) {c i : ℕ}
    (h : m ≤ c ∨ n ≤ i) : coord (ofFn β) c i = 0 := by
  simp only [ofFn, coord_packRows, Nat.not_lt_zero, ite_false, Nat.sub_zero]
  by_cases hc : c < m
  · have hi : ¬i < n := by omega
    simp [hc, hi]
  · simp [hc]

/-- The constructor introduces no extra colours. -/
theorem colours_ofFn_le {m n : ℕ} (β : Fin m → Fin n → ℕ) : colours (ofFn β) ≤ m := by
  simpa [ofFn] using colours_packRows_le (List.ofFn fun c => List.ofFn (β c)) 0

/-- Compression preserves weighted multiplicity exactly. -/
theorem mass_ofFn {m n : ℕ} (β : Fin m → Fin n → ℕ) :
    mass (ofFn β) = ∑ c, ∑ i : Fin n, (i.val + 1) * β c i := by
  simp only [ofFn, mass_packRows, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  apply sum_congr rfl
  intro c _
  rw [rankMass_eq, List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
  simp

end Cslib.SparseModeTuple
