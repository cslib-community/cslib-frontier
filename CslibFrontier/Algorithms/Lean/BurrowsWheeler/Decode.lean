/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.BurrowsWheeler.Basic

/-!
# Table-driven inversion of the Burrows–Wheeler transform

[BurrowsWheeler1994], Section 4.2, inverts the transform with two tables computed from the last
column `L`: `C[c]`, the number of symbols of `L` smaller than `c`, and the rank array `P`, where
`P[i]` counts the occurrences of `L[i]` in `L[0..i-1]`. The LF-mapping is then the lookup
`T i = P[i] + C[L[i]]`, and the word is decoded by `|L|` such lookups.

For bounded integer alphabets `< σ`, `CslibFrontier.Algorithms.WordRAM.BurrowsWheeler` builds `C`
and `P` in `O(|L| + σ)` Word-RAM instructions and runs the `|L|` LF-step lookups in `O(|L|)`
instructions.

## Main definitions

* `rankTableFrom`, `rankTable`: the rank array `P` of [BurrowsWheeler1994], Section 4.2.
* `lfDecodeTable L C P k r acc`: `k` table-driven LF steps `r ↦ P[r] + C[L[r]]` from row `r`.
* `inverseBwtTable L I C P`: `|L|` table-driven LF steps from row `I`.

## Main results

* `getElem?_rankTable`, `getElem_rankTable`: `P[i] = (L.take i).count L[i]`.
* `lfDecodeTable_eq_lfDecode`: when `C` agrees with `L.countP (· < c)` on symbols of `L`,
  `lfDecodeTable L C (rankTable L)` computes `lfDecode L`.
* `inverseBwtTable_eq_inverseBwt`, `inverseBwtTable_bwt`: table-driven decoding computes
  `inverseBwt (L, I)` and recovers `w` from `bwt w`.

## References

* [BurrowsWheeler1994]
-/

public section

namespace Cslib.Algorithms.Lean.BurrowsWheeler

variable {α : Type*}

/-! ## The rank table -/

section RankTable

variable [DecidableEq α]

/-- `rankTableFrom cnt L` lists, for each position `i`, `cnt L[i]` plus the number of earlier
occurrences of `L[i]`. It is one left-to-right pass with a running count per symbol. -/
@[expose] def rankTableFrom (cnt : α → ℕ) : List α → List ℕ
  | [] => []
  | a :: L => cnt a :: rankTableFrom (Function.update cnt a (cnt a + 1)) L

/-- The rank array `P` of [BurrowsWheeler1994], Section 4.2: `P[i]` is the number of occurrences
of `L[i]` before position `i` (Batteries' `L.countBefore L[i] i`). -/
@[expose] def rankTable (L : List α) : List ℕ := rankTableFrom (fun _ => 0) L

@[simp] theorem length_rankTableFrom :
    ∀ (cnt : α → ℕ) (L : List α), (rankTableFrom cnt L).length = L.length
  | _, [] => rfl
  | cnt, a :: L => by
    simp only [rankTableFrom, List.length_cons, length_rankTableFrom]

@[simp] theorem length_rankTable (L : List α) : (rankTable L).length = L.length :=
  length_rankTableFrom _ L

theorem getElem?_rankTableFrom :
    ∀ (cnt : α → ℕ) (L : List α) (i : ℕ),
      (rankTableFrom cnt L)[i]? = L[i]?.map fun a => cnt a + (L.take i).count a
  | _, [], _ => by simp [rankTableFrom]
  | cnt, a :: L, 0 => by simp [rankTableFrom]
  | cnt, a :: L, i + 1 => by
    rw [rankTableFrom, List.getElem?_cons_succ, getElem?_rankTableFrom, List.getElem?_cons_succ,
      List.take_succ_cons]
    cases L[i]? with
    | none => rfl
    | some b =>
      simp only [Option.map_some, List.count_cons]
      by_cases hab : b = a
      · subst hab
        simp only [Function.update_self, beq_self_eq_true, ite_true]
        rw [Nat.add_right_comm, Nat.add_assoc]
      · simp [hab, Ne.symm hab]

theorem getElem?_rankTable (L : List α) (i : ℕ) :
    (rankTable L)[i]? = L[i]?.map fun a => (L.take i).count a := by
  simp [rankTable, getElem?_rankTableFrom]

theorem getElem_rankTable (L : List α) {i : ℕ} (hi : i < L.length) :
    (rankTable L)[i]'(by rwa [length_rankTable]) = (L.take i).count L[i] := by
  have h := getElem?_rankTable L i
  rw [List.getElem?_eq_getElem (by rwa [length_rankTable]), List.getElem?_eq_getElem hi,
    Option.map_some] at h
  exact Option.some.inj h

end RankTable

/-! ## Table-driven LF decoding -/

/-- `k` LF steps from row `r` with the tables `C` and `P`, prepending the symbols read to `acc`.
Each step reads `L[r]` and `P[r]` and moves to `P[r] + C[L[r]]` ([BurrowsWheeler1994],
Section 4.2). It stops early out of range. -/
@[expose] def lfDecodeTable (L : List α) (C : α → ℕ) (P : List ℕ) :
    ℕ → ℕ → List α → List α
  | 0, _, acc => acc
  | k + 1, r, acc =>
    match L[r]?, P[r]? with
    | some c, some p => lfDecodeTable L C P k (p + C c) (c :: acc)
    | _, _ => acc

/-- Table-driven inverse Burrows–Wheeler transform: `|L|` LF steps from row `I` using `C` and
`P`. -/
@[expose] def inverseBwtTable (L : List α) (I : ℕ) (C : α → ℕ) (P : List ℕ) : List α :=
  lfDecodeTable L C P L.length I []

variable [LinearOrder α]

/-- With `P = rankTable L` and `C` matching `L.countP (· < c)` on every symbol in `L`,
`lfDecodeTable` computes `lfDecode`. -/
theorem lfDecodeTable_eq_lfDecode (L : List α) {C : α → ℕ}
    (hC : ∀ c ∈ L, C c = L.countP (· < c)) :
    ∀ (k r : ℕ) (acc : List α),
      lfDecodeTable L C (rankTable L) k r acc = lfDecode L k r acc
  | 0, _, _ => rfl
  | k + 1, r, acc => by
    rw [lfDecodeTable, lfDecode, getElem?_rankTable]
    cases h : L[r]? with
    | none => rfl
    | some c =>
      obtain ⟨hr, rfl⟩ := List.getElem?_eq_some_iff.mp h
      simp only [Option.map_some]
      rw [lfDecodeTable_eq_lfDecode L hC k, lfMap, h, hC _ (List.getElem_mem hr), Nat.add_comm]

theorem inverseBwtTable_eq_inverseBwt (L : List α) (I : ℕ) {C : α → ℕ}
    (hC : ∀ c ∈ L, C c = L.countP (· < c)) :
    inverseBwtTable L I C (rankTable L) = inverseBwt (L, I) :=
  lfDecodeTable_eq_lfDecode L hC L.length I []

/-- Table-driven decoding of `bwt w` recovers `w`. -/
theorem inverseBwtTable_bwt (w : List α) {C : α → ℕ}
    (hC : ∀ c ∈ bwtLast w, C c = (bwtLast w).countP (· < c)) :
    inverseBwtTable (bwtLast w) (bwtIndex w) C (rankTable (bwtLast w)) = w := by
  rw [inverseBwtTable_eq_inverseBwt _ _ hC, ← fst_bwt, ← snd_bwt, Prod.eta, inverseBwt_bwt]

end Cslib.Algorithms.Lean.BurrowsWheeler
