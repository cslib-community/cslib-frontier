/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.Search
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree.Counting
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import CslibFrontier.Foundations.Data.Matrix.Permanent.ZeroOne
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.Set.Finite.List

/-!
# Proposition 6.21 needs negative entries (Goldreich, Exercise 6.25)

Goldreich's Proposition 6.21 maps a 3CNF formula `φ` with `m` clauses to an integer matrix with
entries in a fixed finite set `I` whose permanent is `c ^ m · #3SAT(φ)`, for an even `c > 0`
(`Cslib.Complexity.goldreich_prop_6_21` proves it with `c = 12` and `I = {-1, 0, 1, 2, 3}`).
[Goldreich, Exercise 6.25][Goldreich2007Draft] (February 2007 `r3.pdf`, PDF p. 58 / printed
p. 260) asks to prove that, assuming `P ≠ NP`, no such reduction exists when `I` contains only
non-negative integers, even when `I` is infinite.

The source's guideline is followed. A matrix with non-negative entries has a non-zero permanent
exactly when some permutation runs along non-zero entries
(`Matrix.permanent_ne_zero_iff_of_nonneg`), that is, when the bipartite graph of its support has
a perfect matching (`Cslib.Complexity.intPermanent_ne_zero_iff_zeroOnePermanent_supportTable`).
Perfect matchings are found in polynomial time
(`Cslib.Complexity.BipartitePerfectMatching.searchRel_mem_FPSearch`), so such a reduction would
decide `3SAT` in polynomial time, and `3SAT` is `NP`-complete.

## Main definitions

* `Cslib.Complexity.supportTable`: the Boolean table of the non-zero entries of an integer table.

## Main results

* `Cslib.Complexity.intPermanent_ne_zero_iff_zeroOnePermanent_supportTable`: a non-negative
  integer table has a non-zero permanent exactly when its support has one.
* `Cslib.Complexity.exercise_6_25`: Goldreich's Exercise 6.25.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The **support** of an integer table: the Boolean table of the same shape whose entry is
`true` exactly where the integer entry is non-zero. -/
@[expose] def supportTable (A : List (List ℤ)) : List (List Bool) :=
  A.map fun row => row.map fun x => decide (x ≠ 0)

/-- The support of a dense integer table is computable in polynomial time. -/
theorem computableInPolyTime_supportTable :
    ComputableInPolyTime supportTable encIntTable encBoolTable := by
  have hsup : supportTable = fun A => A.map fun row => row.map fun x => decide (0 < x.natAbs) :=
    funext fun _ => by simp [supportTable]
  rw [hsup]
  fun_prop

theorem length_supportTable (A : List (List ℤ)) : (supportTable A).length = A.length :=
  List.length_map _

/-- The 0/1 matrix of the support is the support of the integer matrix, reindexed along the
equal lengths of the two tables. -/
private theorem boolTableMatrix_supportTable (A : List (List ℤ)) :
    boolTableMatrix (supportTable A) =
      ((tableMatrix A).map fun x => if x ≠ 0 then (1 : ℕ) else 0).submatrix
        (finCongr (length_supportTable A)) (finCongr (length_supportTable A)) := by
  ext i j
  rw [boolTableMatrix_apply, Matrix.submatrix_apply, Matrix.map_apply, tableMatrix_apply,
    show (supportTable A)[i] = (A[i.val]'(length_supportTable A ▸ i.isLt)).map fun x =>
      decide (x ≠ 0) from List.getElem_map _,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  change _ = ite (((A[i.val]'_)[j.val]?).getD 0 ≠ 0) 1 0
  cases (A[i.val]'(length_supportTable A ▸ i.isLt))[j.val]? with
  | none => simp
  | some x => by_cases hx : x = 0 <;> simp [hx]

/-- **A non-negative table has a non-zero permanent exactly when its support does.** The
permanent of a table of non-negative integers is non-zero exactly when the 0/1 permanent of its
support, the number of perfect matchings of the bipartite graph of its non-zero entries, is
non-zero. -/
theorem intPermanent_ne_zero_iff_zeroOnePermanent_supportTable {A : List (List ℤ)}
    (hA : ∀ row ∈ A, ∀ x ∈ row, 0 ≤ x) :
    IntPermanent A ≠ 0 ↔ ZeroOnePermanent (supportTable A) ≠ 0 := by
  have hM : ∀ i j, 0 ≤ tableMatrix A i j := fun i j => by
    rw [tableMatrix_apply, List.getD_eq_getElem?_getD]
    cases h : A[i][j.val]? with
    | none => exact le_rfl
    | some x => exact hA _ (List.getElem_mem _) x (List.mem_of_getElem? h)
  rw [ZeroOnePermanent, boolTableMatrix_supportTable, Matrix.permanent_submatrix_equiv,
    IntPermanent, Matrix.permanent_ne_zero_iff_of_nonneg hM,
    Matrix.permanent_ne_zero_iff_of_nonneg fun _ _ => Nat.zero_le _]
  simp only [Matrix.map_apply]
  refine exists_congr fun σ => forall_congr' fun i => ?_
  split_ifs <;> simp_all

/-- On every formula of clause width at most three, the reduction's permanent is non-zero
exactly on satisfiable formulas; other formulas go to the `1 × 1` zero table. Testing for a
perfect matching of the support therefore decides `3SAT`. -/
private theorem threeSAT_mem_P_of_nonneg {c : ℤ} (hc : c ≠ 0) {r : CNF ℕ → List (List ℤ)}
    (hr : ComputableInPolyTime r encCNF encIntTable)
    (h : ∀ φ : CNF ℕ, (∀ C ∈ φ, C.length ≤ 3) →
      (∀ row ∈ r φ, ∀ x ∈ row, 0 ≤ x) ∧ IntPermanent (r φ) = c ^ φ.length * SharpThreeSAT φ) :
    ThreeSAT ∈ P encCNF := by
  have hdom (B : List (List Bool)) :
      B ∈ searchDomain BipartitePerfectMatching.searchRel ↔ ZeroOnePermanent B ≠ 0 := by
    have hfin : Finite {w // BipartitePerfectMatching.searchRel B w} :=
      ((List.finite_length_eq Bool (B.length * B.length)).subset
        (t := {w | BipartitePerfectMatching.searchRel B w}) fun _ hw => hw.1).to_subtype
    rw [mem_searchDomain, ← bipartitePerfectMatchingCount_eq_zeroOnePermanent,
      ← BipartitePerfectMatching.searchCount_searchRel, searchCount, Nat.card_ne_zero]
    simp only [nonempty_subtype, hfin, and_true]
  refine PolyTimeReducible.mem_P ⟨fun φ => if φ.all fun C => decide (C.length ≤ 3) then
    supportTable (r φ) else [[false]], ?_, fun φ => ?_⟩
    (searchDomain_mem_P BipartitePerfectMatching.searchRel_mem_FPSearch)
  · have := computableInPolyTime_supportTable.comp hr
    unfold encCNF at hr this ⊢
    fun_prop
  · dsimp only
    rw [SharpThreeSAT.mem_ThreeSAT_iff]
    split_ifs with hφ
    · obtain ⟨hnn, hperm⟩ := h φ (by simpa using hφ)
      rw [hdom, ← intPermanent_ne_zero_iff_zeroOnePermanent_supportTable hnn, hperm]
      simp [hc, Nat.pos_iff_ne_zero]
    · rw [hdom, show SharpThreeSAT φ = 0 by simp [SharpThreeSAT, hφ]]
      simp [ZeroOnePermanent, Matrix.permanent_unique, boolTableMatrix_apply]

/-- **Goldreich, Exercise 6.25.** Assuming `P ≠ NP`, Proposition 6.21 fails for every set `I` of
non-negative integers, finite or not: there is no non-zero integer `c` and no polynomial-time map
`r` from formulas to dense integer tables (`encCNF` to `encIntTable`) such that, for every formula
`φ` whose clauses have at most three literals, `r φ` has entries in `I` and permanent
`c ^ m · #3SAT(φ)`, where `m` is the number of clauses of `φ`.

This negates more than the source's statement asserts: `c` need not be even or positive, `I`
need not be finite, and the identity is required on 3CNF formulas only, the inputs of
Proposition 6.21 (`goldreich_prop_6_21` states it on all formulas). As there, `#3SAT` is
`SharpThreeSAT`, the number of satisfying assignments of the variables occurring in `φ`. The
hypothesis `P enc ≠ NP enc` may be taken for any encoding, since `P = NP` does not depend on it. -/
theorem exercise_6_25 {β : Type} {enc : β ↪ List Bool} (hPNP : P enc ≠ NP enc) :
    ¬ ∃ c : ℤ, c ≠ 0 ∧ ∃ I : Set ℤ, (∀ x ∈ I, 0 ≤ x) ∧ ∃ r : CNF ℕ → List (List ℤ),
      ComputableInPolyTime r encCNF encIntTable ∧
      ∀ φ : CNF ℕ, (∀ C ∈ φ, C.length ≤ 3) →
        (∀ row ∈ r φ, ∀ x ∈ row, x ∈ I) ∧ IntPermanent (r φ) = c ^ φ.length * SharpThreeSAT φ := by
  rintro ⟨c, hc, I, hI, r, hr, h⟩
  refine hPNP (ThreeSAT_npComplete.P_eq_NP_of_mem_P (threeSAT_mem_P_of_nonneg hc hr
    fun φ hφ => ?_) enc)
  obtain ⟨hmem, hperm⟩ := h φ hφ
  exact ⟨fun row hrow x hx => hI x (hmem row hrow x hx), hperm⟩

end Cslib.Complexity
