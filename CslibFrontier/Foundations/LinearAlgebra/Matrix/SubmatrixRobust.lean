/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.CutRank
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Submatrix-robust matrices

A matrix is *submatrix-robust* with deficiency `t` (`Matrix.SubmatrixRobust`) when every square
block of it, with `k` rows and `k` columns, has rank at least `k - t`; then every block has rank
at least its smaller side minus `t` (`Matrix.SubmatrixRobust.min_le`).

**Existence by counting** (`Matrix.exists_submatrixRobust`). A square block of an `m × m` matrix
over `𝔽₂` with `k` rows and rank `r` has `r` columns spanning all of its columns. So the matrix is
determined by those columns, the coefficients expressing each other column of the block in terms
of them, and its entries outside the remaining `k × (k - r)` block. Counting these descriptions, at
most `2 ^ (m² - (k - r)²)` matrices are deficient by `k - r` on given sets of rows and columns with
a given spanning set. A union bound over the fewer than `2 ^ (3 m)` choices shows that some matrix
has every square block of rank at least `k - t` once `(t + 1)² > 3 m`. The deficiency
`t = 2 ⌊√m⌋ + 1` qualifies.

**Cut ranks of bilinear forms** (`Matrix.SubmatrixRobust.le_cutRank_add`). Place a robust `k × k`
matrix `R` on a block of a square matrix `M` whose rows and columns are disjoint sets of indices,
with zeros elsewhere, so that the quadratic form of `M` is a bilinear form `xᵀ R y`. A set `U` of
indices cuts the rows of `R` into `x ∩ U` and `x \ U`, and its columns likewise; the block of the
polar matrix `M + Mᵀ` with rows `U` and columns `Uᶜ` contains, on disjoint sets of columns, the
block of `R` with rows `x ∩ U` and columns `y \ U` and the transpose of the block with rows `x \ U`
and columns `y ∩ U` (`Matrix.add_blockRank_le_cutRank_add_transpose`). If there are at most
`2 k + 1` indices and `|U| = k`, the two blocks have total rank at least `k - 1 - 2 t`.

## Main definitions

* `Matrix.SubmatrixRobust M t`: every square block of `M` with `k` rows has rank at least `k - t`.
* `Matrix.DisjointBlockRobust M t`: every square block of `M` on disjoint row and column sets with
  `k` rows has rank at least `k - t`.
* `Matrix.UpperIdx`, `Matrix.toUpper`, `Matrix.polarUpper`: strict upper-triangular index pairs,
  strict upper-triangular matrices, and their symmetric hollow polar matrices `M + Mᵀ`.

## Main results

* `Matrix.SubmatrixRobust.min_le`: every block of a robust matrix has nearly full rank.
* `Matrix.DisjointBlockRobust.min_le`, `Matrix.DisjointBlockRobust.min_le_cutRank_add`: every
  disjoint block (and every cut) of a disjoint-block-robust matrix has nearly full rank.
* `Matrix.exists_submatrixRobust_of_lt`, `Matrix.exists_submatrixRobust`: robust matrices over
  `𝔽₂` exist, by counting.
* `Matrix.exists_polarUpper_disjointBlockRobust`, `Matrix.exists_disjointBlockRobust_of_lt`,
  `Matrix.exists_disjointBlockRobust`: strict upper-triangular matrices over `𝔽₂` with
  disjoint-block-robust polar matrices exist, by counting.
* `Matrix.add_blockRank_le_cutRank_add_transpose`: the cut rank of a bilinear form.
* `Matrix.SubmatrixRobust.le_cutRank_add`: bisections of a robust bilinear form have nearly full
  cut rank.
-/

@[expose] public section

namespace Matrix

variable {m n ι κ κ' K : Type*} [Field K]

/-- `M` is *submatrix-robust* with deficiency `t`: every square block of `M`, with `k` rows and `k`
columns, has rank at least `k - t`. Both index types are required to be finite so that `Set.ncard`
and `Matrix.blockRank` (`Module.finrank`) measure actual block sizes and ranks rather than
returning `0` on infinite sets or subspaces. -/
-- Finiteness restricts the public domain; `ncard` and `finrank` themselves do not require it.
@[nolint unusedArguments]
def SubmatrixRobust [Finite m] [Finite n] (M : Matrix m n K) (t : ℕ) : Prop :=
  ∀ (S : Set m) (T : Set n), S.ncard = T.ncard → S.ncard ≤ M.blockRank S T + t

/-- A larger deficiency is weaker. -/
theorem SubmatrixRobust.mono [Finite m] [Finite n] {M : Matrix m n K} {t t' : ℕ}
    (hM : M.SubmatrixRobust t) (ht : t ≤ t') : M.SubmatrixRobust t' :=
  fun S T h => (hM S T h).trans (Nat.add_le_add_left ht _)

/-- Every block of a robust matrix has rank at least its smaller side minus the deficiency. -/
theorem SubmatrixRobust.min_le [Finite m] [Finite n] {M : Matrix m n K} {t : ℕ}
    (hM : M.SubmatrixRobust t) (S : Set m) (T : Set n) :
    min S.ncard T.ncard ≤ M.blockRank S T + t := by
  obtain ⟨S', hS', hS'c⟩ := Set.exists_subset_card_eq (min_le_left S.ncard T.ncard)
  obtain ⟨T', hT', hT'c⟩ := Set.exists_subset_card_eq (min_le_right S.ncard T.ncard)
  have h := hM S' T' (hS'c.trans hT'c.symm)
  rw [hS'c] at h
  exact h.trans (Nat.add_le_add_right (M.blockRank_mono hS' hT') t)

/-- `M` is *disjoint-block-robust* with deficiency `t`: every square block `S × T` of `M` on
disjoint index sets `S` and `T` with `k` rows and `k` columns has rank at least `k - t`. -/
@[nolint unusedArguments]
def DisjointBlockRobust [Finite ι] (M : Matrix ι ι K) (t : ℕ) : Prop :=
  ∀ (S T : Set ι), Disjoint S T → S.ncard = T.ncard → S.ncard ≤ M.blockRank S T + t

/-- A larger deficiency is weaker. -/
theorem DisjointBlockRobust.mono [Finite ι] {M : Matrix ι ι K} {t t' : ℕ}
    (hM : M.DisjointBlockRobust t) (ht : t ≤ t') : M.DisjointBlockRobust t' :=
  fun S T hST hcard => (hM S T hST hcard).trans (Nat.add_le_add_left ht _)

/-- Every disjoint block of a disjoint-block-robust matrix has rank at least its smaller side minus
the deficiency. -/
theorem DisjointBlockRobust.min_le [Finite ι] {M : Matrix ι ι K} {t : ℕ}
    (hM : M.DisjointBlockRobust t) {S T : Set ι} (hST : Disjoint S T) :
    min S.ncard T.ncard ≤ M.blockRank S T + t := by
  obtain ⟨S', hS', hS'c⟩ := Set.exists_subset_card_eq (min_le_left S.ncard T.ncard)
  obtain ⟨T', hT', hT'c⟩ := Set.exists_subset_card_eq (min_le_right S.ncard T.ncard)
  have h := hM S' T' (hST.mono hS' hT') (hS'c.trans hT'c.symm)
  rw [hS'c] at h
  exact h.trans (Nat.add_le_add_right (M.blockRank_mono hS' hT') t)

/-- Every cut `U` of a disjoint-block-robust matrix has cut rank at least `min |U| |Uᶜ| - t`. -/
theorem DisjointBlockRobust.min_le_cutRank_add [Finite ι] {M : Matrix ι ι K} {t : ℕ}
    (hM : M.DisjointBlockRobust t) (U : Set ι) :
    min U.ncard Uᶜ.ncard ≤ M.cutRank U + t :=
  hM.min_le disjoint_compl_right

/-! ### Existence by counting -/

section Counting

open Finset

variable {k : ℕ}

/-- The column `j` of `R`, restricted to the rows `S`. -/
private def colVec (R : Matrix (Fin k) (Fin k) (ZMod 2)) (S : Set (Fin k)) (j : Fin k) :
    S → ZMod 2 :=
  fun i => R i j

/-- **Column bases.** The columns of a block contain a spanning set as large as the rank of the
block. -/
private theorem exists_spanning_columns (R : Matrix (Fin k) (Fin k) (ZMod 2))
    (S T : Finset (Fin k)) :
    ∃ T' ⊆ T, #T' = R.blockRank ↑S ↑T ∧
      ∀ j ∈ T, colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T') := by
  classical
  let v : (↑T : Set (Fin k)) → (↑S : Set (Fin k)) → ZMod 2 := fun j => colVec R ↑S j
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' (ZMod 2) v
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  refine ⟨Finset.univ.image fun x => (a x : Fin k), ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨x, -, rfl⟩ := mem_image.mp hj
    exact (a x).2
  · rw [show (fun x => (a x : Fin k)) = Subtype.val ∘ a from rfl,
      card_image_of_injective _ (Subtype.val_injective.comp ha), card_univ,
      ← finrank_span_eq_card hli, hspan, ← blockRank_transpose]
    rfl
  · have hrange :
        Set.range (v ∘ a) = colVec R ↑S '' ↑(Finset.univ.image fun x => (a x : Fin k)) := by
      ext y
      simp only [Set.mem_range, Function.comp_apply, coe_image, coe_univ, Set.image_univ,
        Set.mem_image, v]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨a x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    intro j hj
    rw [← hrange, hspan]
    exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

open Classical in
/-- Parameters `a : α` whose columns in `T`, restricted to the rows `S`, lie in the span of their
columns in `T'`. -/
private noncomputable def spannedFamily {α : Type*} [Fintype α]
    (mat : α → Matrix (Fin k) (Fin k) (ZMod 2)) (S T T' : Finset (Fin k)) : Finset α :=
  {a | ∀ j ∈ T, colVec (mat a) ↑S j ∈ Submodule.span (ZMod 2) (colVec (mat a) ↑S '' ↑T')}

open Classical in
/-- Coefficients expressing a column in terms of the columns in `T'`, chosen once and for all. -/
private noncomputable def spanCoeff (R : Matrix (Fin k) (Fin k) (ZMod 2)) (S T' : Finset (Fin k))
    (j : Fin k) : T' → ZMod 2 :=
  if h : colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T') then
    Classical.choose ((Submodule.mem_span_image_finset_iff_exists_fun (ZMod 2)).mp h)
  else 0

private theorem spanCoeff_spec {R : Matrix (Fin k) (Fin k) (ZMod 2)} {S T' : Finset (Fin k)}
    {j : Fin k} (h : colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T')) :
    ∑ l, spanCoeff R S T' j l • colVec R ↑S l = colVec R ↑S j := by
  unfold spanCoeff
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec ((Submodule.mem_span_image_finset_iff_exists_fun (ZMod 2)).mp h)

/-- When `T' ⊆ T`, `#T' + t < #S`, and `#S = #T`, a codimension bound on `spannedFamily mat S T T'`
gives `#(spannedFamily mat S T T') * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ U`. -/
private theorem card_spannedFamily_mul_two_pow_sq_le {α : Type*} [Fintype α] {U t : ℕ}
    {mat : α → Matrix (Fin k) (Fin k) (ZMod 2)} {S T T' : Finset (Fin k)}
    (H : #(spannedFamily mat S T T') * 2 ^ (#S * #(T \ T')) ≤ 2 ^ (#(T \ T') * #T') * 2 ^ U)
    (hT'T : T' ⊆ T) (hlt : #T' + t < #S) (hST : #S = #T) :
    #(spannedFamily mat S T T') * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ U := by
  have hsplit := card_sdiff_add_card_eq_card hT'T
  set d := #(T \ T')
  have hd : t + 1 ≤ d := by omega
  rw [hST, ← hsplit] at H
  have hpow : 2 ^ ((t + 1) ^ 2) ≤ 2 ^ (d * d) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have key : #(spannedFamily mat S T T') * 2 ^ (d * d) * 2 ^ (d * #T') ≤
      2 ^ U * 2 ^ (d * #T') := by
    calc #(spannedFamily mat S T T') * 2 ^ (d * d) * 2 ^ (d * #T')
        = #(spannedFamily mat S T T') * 2 ^ ((d + #T') * d) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          ring
      _ ≤ 2 ^ (d * #T') * 2 ^ U := H
      _ = _ := mul_comm _ _
  calc #(spannedFamily mat S T T') * 2 ^ ((t + 1) ^ 2)
      ≤ #(spannedFamily mat S T T') * 2 ^ (d * d) := Nat.mul_le_mul_left _ hpow
    _ ≤ _ := Nat.le_of_mul_le_mul_right key (by positivity)

open Classical in
/-- Parameters `a : α` whose `P`-admissible square block `S × T` has deficiency larger than `t`. -/
private noncomputable def deficientFamily {α : Type*} [Fintype α]
    (P : Finset (Fin k) → Finset (Fin k) → Prop)
    (mat : α → Matrix (Fin k) (Fin k) (ZMod 2)) (t : ℕ) (S T : Finset (Fin k)) : Finset α :=
  {a | P S T ∧ #S = #T ∧ (mat a).blockRank ↑S ↑T + t < #S}

private theorem card_deficientFamily_mul_le {α : Type*} [Fintype α] {U : ℕ}
    {P : Finset (Fin k) → Finset (Fin k) → Prop}
    {mat : α → Matrix (Fin k) (Fin k) (ZMod 2)}
    (hspan : ∀ {S T T' : Finset (Fin k)}, P S T → T' ⊆ T →
      #(spannedFamily mat S T T') * 2 ^ (#S * #(T \ T')) ≤ 2 ^ (#(T \ T') * #T') * 2 ^ U)
    (t : ℕ) (S T : Finset (Fin k)) :
    #(deficientFamily P mat t S T) * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ k * 2 ^ U := by
  classical
  let 𝒯 := T.powerset.filter fun T' => P S T ∧ #T' + t < #S ∧ #S = #T
  have hsub : deficientFamily P mat t S T ⊆ 𝒯.biUnion fun T' => spannedFamily mat S T T' := by
    intro a ha
    obtain ⟨hP, hST, hdef⟩ := (mem_filter.mp ha).2
    obtain ⟨T', hT', hcard, hsp⟩ := exists_spanning_columns (mat a) S T
    refine mem_biUnion.mpr ⟨T', mem_filter.mpr ⟨mem_powerset.mpr hT', hP, by omega, hST⟩, ?_⟩
    exact mem_filter.mpr ⟨mem_univ _, hsp⟩
  have hone : ∀ T' ∈ 𝒯, #(spannedFamily mat S T T') * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ U :=
    fun T' hT' => by
      obtain ⟨hT'T, hP, hlt, hST⟩ := mem_filter.mp hT'
      exact card_spannedFamily_mul_two_pow_sq_le (hspan hP (mem_powerset.mp hT'T))
        (mem_powerset.mp hT'T) hlt hST
  have h𝒯 : #𝒯 ≤ 2 ^ k := by
    calc #𝒯 ≤ #T.powerset := card_filter_le _ _
      _ = 2 ^ #T := card_powerset T
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (card_le_univ T |>.trans (by simp))
  calc #(deficientFamily P mat t S T) * 2 ^ ((t + 1) ^ 2)
      ≤ (∑ T' ∈ 𝒯, #(spannedFamily mat S T T')) * 2 ^ ((t + 1) ^ 2) :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ T' ∈ 𝒯, #(spannedFamily mat S T T') * 2 ^ ((t + 1) ^ 2) := Finset.sum_mul ..
    _ ≤ ∑ _T' ∈ 𝒯, 2 ^ U := Finset.sum_le_sum hone
    _ = #𝒯 * 2 ^ U := by rw [sum_const, smul_eq_mul]
    _ ≤ 2 ^ k * 2 ^ U := Nat.mul_le_mul_right _ h𝒯

open Classical in
/-- **Shared counting union bound.** For any `2 ^ U`-element matrix family satisfying the
`spannedFamily` codimension bound on `P`-admissible blocks, `3 k < (t + 1) ^ 2` guarantees an
element with deficiency at most `t` on every `P`-admissible square block. -/
private theorem exists_blockRank_ge_of_spanned_bound {α : Type*} [Fintype α] {U t : ℕ}
    (hα : Fintype.card α = 2 ^ U) (mat : α → Matrix (Fin k) (Fin k) (ZMod 2))
    (P : Finset (Fin k) → Finset (Fin k) → Prop)
    (hspan : ∀ {S T T' : Finset (Fin k)}, P S T → T' ⊆ T →
      #(spannedFamily mat S T T') * 2 ^ (#S * #(T \ T')) ≤ 2 ^ (#(T \ T') * #T') * 2 ^ U)
    (ht : 3 * k < (t + 1) ^ 2) :
    ∃ a : α, ∀ S T : Set (Fin k), P S.toFinset T.toFinset → S.ncard = T.ncard →
      S.ncard ≤ (mat a).blockRank S T + t := by
  classical
  let pairs : Finset (Finset (Fin k) × Finset (Fin k)) := univ ×ˢ univ
  let bad := pairs.biUnion fun p => deficientFamily P mat t p.1 p.2
  have hbad : #bad * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ k * 2 ^ k * (2 ^ k * 2 ^ U) := by
    calc #bad * 2 ^ ((t + 1) ^ 2)
        ≤ (∑ p ∈ pairs, #(deficientFamily P mat t p.1 p.2)) * 2 ^ ((t + 1) ^ 2) :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ p ∈ pairs, #(deficientFamily P mat t p.1 p.2) * 2 ^ ((t + 1) ^ 2) := Finset.sum_mul ..
      _ ≤ ∑ _p ∈ pairs, 2 ^ k * 2 ^ U :=
          Finset.sum_le_sum fun p _ => card_deficientFamily_mul_le hspan t p.1 p.2
      _ = 2 ^ k * 2 ^ k * (2 ^ k * 2 ^ U) := by
          rw [sum_const, smul_eq_mul, card_product, card_univ, Fintype.card_finset,
            Fintype.card_fin]
  have hlt : #bad < Fintype.card α := by
    refine Nat.lt_of_mul_lt_mul_right (a := 2 ^ ((t + 1) ^ 2)) (hbad.trans_lt ?_)
    rw [hα, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨a, -, ha⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨a, fun S T hP hST => not_lt.mp fun hcon => ha ?_⟩
  refine mem_biUnion.mpr ⟨(S.toFinset, T.toFinset), mem_product.mpr ⟨mem_univ _, mem_univ _⟩,
    mem_filter.mpr ⟨mem_univ _, hP, ?_, ?_⟩⟩
  · simpa only [Set.ncard_eq_toFinset_card'] using hST
  · simpa only [Set.coe_toFinset, Set.ncard_eq_toFinset_card'] using hcon

private theorem three_mul_lt_sq_two_mul_sqrt (k : ℕ) :
    3 * k < (2 * Nat.sqrt k + 1 + 1) ^ 2 := by
  have h := Nat.lt_succ_sqrt' k
  have hsq : (2 * Nat.sqrt k + 1 + 1) ^ 2 = 4 * (Nat.sqrt k + 1) ^ 2 := by ring
  rw [hsq]
  rw [Nat.succ_eq_add_one] at h
  omega

/-- **Counting spanned families.** Let the entries of `mat u` on `S × T` be distinct coordinates
`u (e p)` of `u`. A parameter in `spannedFamily mat S T T'` is determined by the coefficients of
its columns in `T \ T'` and by its coordinates outside `e (S × (T \ T'))`. -/
private theorem card_spannedFamily_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {mat : (ι → ZMod 2) → Matrix (Fin k) (Fin k) (ZMod 2)} {S T T' : Finset (Fin k)}
    (hT'T : T' ⊆ T) (e : S × T → ι) (he : Function.Injective e)
    (hmat : ∀ u (p : S × T), mat u p.1 p.2 = u (e p)) :
    #(spannedFamily mat S T T') * 2 ^ (#S * #(T \ T')) ≤
      2 ^ (#(T \ T') * #T') * 2 ^ Fintype.card ι := by
  classical
  set D := T \ T'
  have hDT (j : D) : j.1 ∈ T := (mem_sdiff.mp j.2).1
  let W : Finset ι := univ.image fun p : S × D => e (p.1, ⟨p.2, hDT p.2⟩)
  have hcardW : #W = #S * #D := by
    refine (card_image_of_injective _ fun p q h => ?_).trans (by simp)
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (he h)
    exact Prod.ext h₁ (Subtype.ext (Subtype.mk.inj h₂))
  let Φ : (ι → ZMod 2) → (D → T' → ZMod 2) × (↥Wᶜ → ZMod 2) :=
    fun u => (fun j => spanCoeff (mat u) S T' j, fun q => u q)
  have hinj : Set.InjOn Φ (spannedFamily mat S T T') := by
    intro u₁ h₁ u₂ h₂ h
    obtain ⟨hc, hz⟩ := Prod.mk.inj h
    funext q
    by_cases hq : q ∈ Wᶜ
    · exact congrFun hz ⟨q, hq⟩
    simp only [mem_compl, not_not, W, mem_image, mem_univ, true_and] at hq
    obtain ⟨⟨i, j⟩, rfl⟩ := hq
    have e₁ := congrFun (spanCoeff_spec ((mem_filter.mp h₁).2 j (hDT j))) i
    have e₂ := congrFun (spanCoeff_spec ((mem_filter.mp h₂).2 j (hDT j))) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colVec] at e₁ e₂
    rw [← hmat u₁ (i, ⟨j, hDT j⟩), ← hmat u₂ (i, ⟨j, hDT j⟩), ← e₁, ← e₂, congrFun hc j]
    refine Finset.sum_congr rfl fun l _ => congrArg _ ?_
    have hl : e (i, ⟨l, hT'T l.2⟩) ∈ Wᶜ := by
      simp only [W, mem_compl, mem_image, mem_univ, true_and, not_exists]
      intro p hp
      have hpl : p.2.1 = l.1 := congrArg (fun x => x.2.1) (he hp)
      exact (mem_sdiff.mp p.2.2).2 (hpl ▸ l.2)
    rw [hmat u₁ (i, ⟨l, _⟩), hmat u₂ (i, ⟨l, _⟩)]
    exact congrFun hz ⟨_, hl⟩
  have hcard := card_le_card_of_injOn Φ (fun _ _ => mem_univ _) hinj
  rw [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    ZMod.card, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe] at hcard
  calc #(spannedFamily mat S T T') * 2 ^ (#S * #D)
      ≤ (2 ^ #T') ^ #D * 2 ^ #Wᶜ * 2 ^ (#S * #D) := Nat.mul_le_mul_right _ hcard
    _ = 2 ^ (#D * #T') * 2 ^ Fintype.card ι := by
        rw [mul_assoc, ← pow_add, ← hcardW, card_compl_add_card, ← pow_mul, mul_comm #T']

/-- **Robust matrices exist, by counting.** If `3 k < (t + 1)²`, some `k × k` matrix over `𝔽₂` is
submatrix-robust with deficiency `t`. -/
theorem exists_submatrixRobust_of_lt {t : ℕ} (ht : 3 * k < (t + 1) ^ 2) :
    ∃ R : Matrix (Fin k) (Fin k) (ZMod 2), R.SubmatrixRobust t := by
  classical
  obtain ⟨u, hu⟩ := exists_blockRank_ge_of_spanned_bound (by rw [Fintype.card_fun, ZMod.card])
    (fun u : Fin k × Fin k → ZMod 2 => Matrix.of fun i j => u (i, j)) (fun _ _ => True)
    (fun _ hT'T => card_spannedFamily_mul_le hT'T (fun p => (p.1.1, p.2.1))
      (fun _ _ h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))) fun _ _ => rfl) ht
  exact ⟨_, fun S T hST => hu S T trivial hST⟩

/-- **Robust matrices exist.** For every `k`, some `k × k` matrix over `𝔽₂` has every square block
with `j` rows of rank at least `j - (2 ⌊√k⌋ + 1)`. -/
theorem exists_submatrixRobust (k : ℕ) :
    ∃ R : Matrix (Fin k) (Fin k) (ZMod 2), R.SubmatrixRobust (2 * Nat.sqrt k + 1) :=
  exists_submatrixRobust_of_lt (three_mul_lt_sq_two_mul_sqrt k)

/-- Strict upper-triangular index pairs `(i, j)` of `Fin n` with `i < j`. -/
abbrev UpperIdx (n : ℕ) : Type :=
  {p : Fin n × Fin n // p.1 < p.2}

/-- Strict upper-triangular `k × k` matrix determined by its entries `u` above the diagonal. -/
def toUpper {R : Type*} [Zero R] (u : UpperIdx k → R) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i j => if h : i < j then u ⟨(i, j), h⟩ else 0

/-- The symmetric hollow polar matrix `toUpper u + (toUpper u)ᵀ` associated to `u`. -/
def polarUpper {R : Type*} [AddZeroClass R] (u : UpperIdx k → R) : Matrix (Fin k) (Fin k) R :=
  toUpper u + (toUpper u)ᵀ

theorem polarUpper_eq {R : Type*} [AddZeroClass R] (u : UpperIdx k → R) :
    polarUpper u = toUpper u + (toUpper u)ᵀ :=
  rfl

private def ordPair {i j : Fin k} (hne : i ≠ j) : UpperIdx k :=
  ⟨(min i j, max i j), min_lt_max.mpr hne⟩

private theorem polarUpper_apply_of_ne (u : UpperIdx k → ZMod 2) {i j : Fin k}
    (hne : i ≠ j) : polarUpper u i j = u (ordPair hne) := by
  rcases hne.lt_or_gt with h | h <;>
    simp [polarUpper, toUpper, ordPair, Function.swap, h, lt_asymm h, h.le]

private theorem ordPair_eq_iff {i₁ j₁ i₂ j₂ : Fin k} (h₁ : i₁ ≠ j₁) (h₂ : i₂ ≠ j₂)
    (heq : ordPair h₁ = ordPair h₂) :
    (i₁ = i₂ ∧ j₁ = j₂) ∨ (i₁ = j₂ ∧ j₁ = i₂) := by
  simp only [ordPair, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_min,
    Fin.val_max] at heq ⊢
  omega

private theorem card_spannedUpper_mul_le {S T T' : Finset (Fin k)}
    (hST : Disjoint S T) (hT'T : T' ⊆ T) :
    #(spannedFamily (polarUpper (k := k)) S T T') * 2 ^ (#S * #(T \ T')) ≤
      2 ^ (#(T \ T') * #T') * 2 ^ Fintype.card (UpperIdx k) := by
  have hne (p : S × T) : p.1.1 ≠ p.2.1 := fun h => disjoint_left.mp hST p.1.2 (h ▸ p.2.2)
  refine card_spannedFamily_mul_le hT'T (fun p => ordPair (hne p)) (fun p q h => ?_)
    fun u p => polarUpper_apply_of_ne u (hne p)
  rcases ordPair_eq_iff _ _ h with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
  · exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
  · exact absurd (h₁ ▸ q.2.2) (disjoint_left.mp hST p.1.2)

/-- **Disjoint-block-robust `polarUpper` witnesses, by counting.** If `3 k < (t + 1) ^ 2`, some
upper-triangular assignment `u : UpperIdx k → ZMod 2` has `(polarUpper u).DisjointBlockRobust t`. -/
theorem exists_polarUpper_disjointBlockRobust_of_lt {t : ℕ} (ht : 3 * k < (t + 1) ^ 2) :
    ∃ u : UpperIdx k → ZMod 2, (polarUpper u).DisjointBlockRobust t := by
  classical
  have hcard : Fintype.card (UpperIdx k → ZMod 2) = 2 ^ Fintype.card (UpperIdx k) := by
    rw [Fintype.card_fun, ZMod.card]
  obtain ⟨u, hu⟩ := exists_blockRank_ge_of_spanned_bound hcard polarUpper Disjoint
    (fun hST hT'T => card_spannedUpper_mul_le hST hT'T) ht
  refine ⟨u, fun S T hST hcard_eq => hu S T ?_ hcard_eq⟩
  rwa [← Finset.disjoint_coe, Set.coe_toFinset, Set.coe_toFinset]

/-- **Polar matrices of upper-triangular forms are disjoint-block-robust, by counting.** If
`3 k < (t + 1) ^ 2`, some `k × k` matrix `Q` over `𝔽₂` has `(Q + Qᵀ).DisjointBlockRobust t`. -/
theorem exists_disjointBlockRobust_of_lt {t : ℕ} (ht : 3 * k < (t + 1) ^ 2) :
    ∃ Q : Matrix (Fin k) (Fin k) (ZMod 2), (Q + Qᵀ).DisjointBlockRobust t := by
  obtain ⟨u, hu⟩ := exists_polarUpper_disjointBlockRobust_of_lt ht
  exact ⟨toUpper u, hu⟩

/-- **Disjoint-block-robust `polarUpper` witnesses exist.** For every `k`, some
`u : UpperIdx k → ZMod 2` has `(polarUpper u).DisjointBlockRobust (2 ⌊√k⌋ + 1)`. -/
theorem exists_polarUpper_disjointBlockRobust (k : ℕ) :
    ∃ u : UpperIdx k → ZMod 2, (polarUpper u).DisjointBlockRobust (2 * Nat.sqrt k + 1) :=
  exists_polarUpper_disjointBlockRobust_of_lt (three_mul_lt_sq_two_mul_sqrt k)

/-- **Disjoint-block-robust polar matrices exist.** For every `k`, some `k × k` matrix `Q` over `𝔽₂`
has `(Q + Qᵀ).DisjointBlockRobust (2 ⌊√k⌋ + 1)`. -/
theorem exists_disjointBlockRobust (k : ℕ) :
    ∃ Q : Matrix (Fin k) (Fin k) (ZMod 2), (Q + Qᵀ).DisjointBlockRobust (2 * Nat.sqrt k + 1) := by
  obtain ⟨u, hu⟩ := exists_polarUpper_disjointBlockRobust k
  exact ⟨toUpper u, hu⟩

end Counting

/-! ### Cut ranks of bilinear forms -/

section Bilinear

open Set

/-- **The cut rank of a bilinear form.** Let `f` and `g` place the rows and the columns of `R`
injectively among the indices of a square matrix `M`, with disjoint ranges, and let `M` carry `R`
on that block and vanish elsewhere. Then at every set `U` of indices, the cut rank of the polar
matrix `M + Mᵀ` is at least the rank of the block of `R` with rows `f⁻¹ U` and columns `g⁻¹ Uᶜ`
plus the rank of the block with rows `f⁻¹ Uᶜ` and columns `g⁻¹ U`. -/
theorem add_blockRank_le_cutRank_add_transpose [Finite ι]
    {R : Matrix κ κ' K} {M : Matrix ι ι K} {f : κ → ι} {g : κ' → ι}
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : Disjoint (range f) (range g))
    (hMR : M.submatrix f g = R) (hM : ∀ i j, i ∉ range f ∨ j ∉ range g → M i j = 0)
    (U : Set ι) :
    R.blockRank (f ⁻¹' U) (g ⁻¹' Uᶜ) + R.blockRank (f ⁻¹' Uᶜ) (g ⁻¹' U) ≤
      (M + Mᵀ).cutRank U := by
  set X := range f
  set Y := range g
  have hMX (i j : ι) (h : i ∉ X) : M i j = 0 := hM i j (Or.inl h)
  have hMY (i j : ι) (h : j ∉ Y) : M i j = 0 := hM i j (Or.inr h)
  have hnotY : ∀ i ∈ X, i ∉ Y := fun i hi hi' => hfg.ne_of_mem hi hi' rfl
  have hnotX : ∀ i ∈ Y, i ∉ X := fun i hi hi' => hfg.ne_of_mem hi' hi rfl
  -- The two blocks of the polar matrix live on the disjoint columns `Y \ U` and `X \ U`.
  have hsum := (M + Mᵀ).add_blockRank_le_of_disjoint (S := U) (T := Uᶜ) (S₁ := U ∩ X)
    (S₂ := U ∩ Y) (T₁ := Uᶜ ∩ Y) (T₂ := Uᶜ ∩ X) inter_subset_left inter_subset_left
    (hfg.symm.mono inter_subset_right inter_subset_right)
    (fun i hi j hj hj' => by simp only [Matrix.add_apply, transpose_apply,
      hMY i j fun h => hj' ⟨hj, h⟩, hMY j i (hnotY i hi.2), add_zero])
    (fun i hi j hj hj' => by simp only [Matrix.add_apply, transpose_apply,
      hMX i j (hnotX i hi.2), hMX j i fun h => hj' ⟨hj, h⟩, add_zero])
  have hb₁ : R.blockRank (f ⁻¹' U) (g ⁻¹' Uᶜ) ≤ (M + Mᵀ).blockRank (U ∩ X) Uᶜ := by
    rw [← hMR, M.blockRank_submatrix hf hg, image_preimage_eq_inter_range,
      image_preimage_eq_inter_range]
    refine (blockRank_congr fun i hi j _ => ?_).trans_le
      (blockRank_mono_right _ _ inter_subset_left)
    simp only [Matrix.add_apply, transpose_apply, hMY j i (hnotY i hi.2), add_zero]
  have hb₂ : R.blockRank (f ⁻¹' Uᶜ) (g ⁻¹' U) ≤ (M + Mᵀ).blockRank (U ∩ Y) Uᶜ := by
    rw [← hMR, M.blockRank_submatrix hf hg, image_preimage_eq_inter_range,
      image_preimage_eq_inter_range, ← M.blockRank_transpose]
    refine (blockRank_congr fun i hi j _ => ?_).trans_le
      (blockRank_mono_right _ _ inter_subset_left)
    simp only [Matrix.add_apply, transpose_apply, hMX i j (hnotX i hi.2), zero_add]
  unfold cutRank
  omega

/-- Two injective maps with disjoint ranges pull back at most `|V|` elements of `V`. -/
theorem ncard_preimage_add_ncard_preimage_le [Finite ι] {f : κ → ι} {g : κ' → ι}
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : Disjoint (range f) (range g))
    (V : Set ι) : (f ⁻¹' V).ncard + (g ⁻¹' V).ncard ≤ V.ncard := by
  rw [← ncard_image_of_injective _ hf, ← ncard_image_of_injective _ hg,
    ← ncard_union_eq (hfg.mono (image_subset_range _ _) (image_subset_range _ _))]
  exact ncard_le_ncard (union_subset (image_preimage_subset _ _) (image_preimage_subset _ _))

/-- **Bisections of a robust bilinear form.** Let `M` carry a `k × k` matrix `R` that is
submatrix-robust with deficiency `t` on a block whose rows and columns are disjoint sets of
indices, and vanish elsewhere, with at most `2 k + 1` indices in all. Then every set `U` of `k`
indices has cut rank at least `k - (2 t + 1)` in the polar matrix `M + Mᵀ`. -/
theorem SubmatrixRobust.le_cutRank_add [Finite ι] {k t : ℕ}
    {R : Matrix (Fin k) (Fin k) K} (hR : R.SubmatrixRobust t) {M : Matrix ι ι K}
    {f g : Fin k → ι} (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : Disjoint (range f) (range g)) (hMR : M.submatrix f g = R)
    (hM : ∀ i j, i ∉ range f ∨ j ∉ range g → M i j = 0) (hι : Nat.card ι ≤ 2 * k + 1)
    {U : Set ι} (hU : U.ncard = k) : k ≤ (M + Mᵀ).cutRank U + (2 * t + 1) := by
  have hsum := add_blockRank_le_cutRank_add_transpose hf hg hfg hMR hM U
  have hr₁ := hR.min_le (f ⁻¹' U) (g ⁻¹' Uᶜ)
  have hr₂ := hR.min_le (f ⁻¹' Uᶜ) (g ⁻¹' U)
  have hcardFin (V : Set (Fin k)) : V.ncard + Vᶜ.ncard = k := by
    rw [ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have ha := hcardFin (f ⁻¹' U)
  have hb := hcardFin (g ⁻¹' U)
  rw [← preimage_compl] at ha hb
  have hU' := ncard_add_ncard_compl U
  have hab := ncard_preimage_add_ncard_preimage_le hf hg hfg U
  have hab' := ncard_preimage_add_ncard_preimage_le hf hg hfg Uᶜ
  omega

end Bilinear

end Matrix
