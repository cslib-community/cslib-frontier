/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rectangle-free Boolean matrices and the `2`-rectangle lift

A Boolean matrix `A : Matrix α β Bool` has *weight* `boolMatrixWeight A`, the number of its `true`
entries, and is *`k`-rectangle-free* (`IsRectangleFreeMatrix A k`, or *`k`-free*) when no
`k`-element row set `I` and `k`-element column set `J` form an all-`true` submatrix `I × J`.

Given `A : Matrix α β Bool`, its *`2`-rectangle lift* `twoRectMatrix A` is indexed by `2`-element
subsets `{r : Finset α // #r = 2}` and `{c : Finset β // #c = 2}`, with entry `(r, c)` equal to
`true` precisely when `r × c` is an all-`true` `2 × 2` submatrix of `A`. Following Sergeev
([Sergeev2014ORComplement], Lemmas 1 and 2, p. 2):

* **Dense `2`-rectangle counting**
  (`pow_four_boolMatrixWeight_le_mul_boolMatrixWeight_twoRectMatrix`, Lemma 1): if an `m × m`
  Boolean matrix `A` has weight `|A| ≥ 2 m^{3/2}` (stated in exact integer form as
  `4 * m ^ 3 ≤ |A| ^ 2`), then `|A| ^ 4 ≤ 32 * m ^ 4 * |twoRectMatrix A|`.
* **Minimum-row-degree `2`-rectangle bound**
  (`mul_sub_le_two_mul_choose_mul_boolMatrixWeight_twoRectMatrix`): if every row of `A` has at
  least `d` ones, then
  `(|α| * C(d, 2)) * (|α| * C(d, 2) - C(|β|, 2)) ≤ 2 * C(|β|, 2) * |twoRectMatrix A|`.
* **Rectangle-freeness of the `2`-rectangle lift** (`IsRectangleFreeMatrix.twoRectMatrix`, Lemma 2):
  if `A` is `k`-free, then `twoRectMatrix A` is `(C(k - 1, 2) + 1)`-free.

## Main definitions

* `Cslib.boolMatrixWeight`: the number of `true` entries in a finite Boolean matrix.
* `Cslib.IsRectangleFreeMatrix`: absence of `k × k` all-`true` submatrices (`k`-freeness).
* `Cslib.twoRectMatrix`: the `C(|α|, 2) × C(|β|, 2)` Boolean matrix indicating `2 × 2` all-`true`
  submatrices of `A`.

## Main results

* `Cslib.mul_sub_le_two_mul_choose_mul_boolMatrixWeight_twoRectMatrix`: lower bound on `2 × 2`
  all-`true` rectangles from a uniform lower bound on row weights.
* `Cslib.pow_four_boolMatrixWeight_le_mul_boolMatrixWeight_twoRectMatrix`: Sergeev's Lemma 1,
  `|A| ^ 4 ≤ 32 * m ^ 4 * |twoRectMatrix A|` when `4 * m ^ 3 ≤ |A| ^ 2`.
* `Cslib.IsRectangleFreeMatrix.twoRectMatrix`: Sergeev's Lemma 2, `twoRectMatrix A` is
  `(C(k - 1, 2) + 1)`-free whenever `A` is `k`-free.

## References

* [I. S. Sergeev, *On relative OR-complexity of Boolean matrices and their
  complements*][Sergeev2014ORComplement], Lemmas 1–2, p. 2
-/

public section

namespace Cslib

open Finset

variable {α β α' β' : Type*}

/-- The *weight* `|A|` of a finite Boolean matrix `A`: the number of entries equal to `true`. -/
@[expose] def boolMatrixWeight [Fintype α] [Fintype β] (A : Matrix α β Bool) : ℕ :=
  #(univ.filter fun p : α × β => A p.1 p.2 = true)

/-- The weight of a Boolean matrix is at most the total number of entries. -/
theorem boolMatrixWeight_le_card_mul [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    boolMatrixWeight A ≤ Fintype.card α * Fintype.card β := by
  simpa only [boolMatrixWeight, Fintype.card_prod, card_univ] using
    card_filter_le (univ : Finset (α × β)) fun p => A p.1 p.2 = true

/-- The weights of a Boolean matrix and its entrywise negation sum to `|α| * |β|`. -/
theorem boolMatrixWeight_add_compl [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    boolMatrixWeight A + boolMatrixWeight (A.map (! ·)) = Fintype.card α * Fintype.card β := by
  unfold boolMatrixWeight
  have h := card_filter_add_card_filter_not
    (s := (univ : Finset (α × β))) (p := fun p => A p.1 p.2 = true)
  rw [card_univ, Fintype.card_prod] at h
  rw [← h]
  congr 3
  ext p
  simp only [Matrix.map_apply, Bool.not_eq_true', Bool.not_eq_true]

/-- The weight of a Boolean matrix equals the sum of its row weights. -/
theorem boolMatrixWeight_eq_sum_row [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    boolMatrixWeight A = ∑ i : α, #(univ.filter fun j : β => A i j = true) := by
  rw [boolMatrixWeight, ← card_sigma]
  refine card_equiv (Equiv.sigmaEquivProd _ _).symm fun p => ?_
  simp only [mem_sigma, mem_univ, mem_filter, true_and]
  rfl

/-- Reindexing rows and columns by equivalences preserves Boolean matrix weight. -/
theorem boolMatrixWeight_reindex [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (e₁ : α ≃ α') (e₂ : β ≃ β') (A : Matrix α β Bool) :
    boolMatrixWeight (Matrix.reindex e₁ e₂ A) = boolMatrixWeight A := by
  unfold boolMatrixWeight
  refine card_equiv (e₁.symm.prodCongr e₂.symm) fun p => ?_
  rw [mem_filter, mem_filter]
  simp only [mem_univ, true_and]
  rfl

/-- A Boolean matrix `A` is *`k`-rectangle-free* (*`k`-free*) if no `k` rows and `k` columns form
an all-`true` `k × k` submatrix ([Sergeev2014ORComplement], p. 1). -/
@[expose] def IsRectangleFreeMatrix (A : Matrix α β Bool) (k : ℕ) : Prop :=
  ∀ (I : Finset α) (J : Finset β), #I = k → #J = k → ¬ (∀ i ∈ I, ∀ j ∈ J, A i j = true)

/-- Every `k`-free matrix has `0 < k`, since the empty `0 × 0` submatrix is vacuously all-`true`. -/
theorem IsRectangleFreeMatrix.pos {A : Matrix α β Bool} {k : ℕ} (hA : IsRectangleFreeMatrix A k) :
    0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact False.elim (hA ∅ ∅ rfl rfl fun i hi => nomatch hi)
  · exact hk

/-- A `1`-free finite Boolean matrix has weight `0`. -/
theorem IsRectangleFreeMatrix.boolMatrixWeight_eq_zero [Fintype α] [Fintype β]
    {A : Matrix α β Bool} (hA : IsRectangleFreeMatrix A 1) : boolMatrixWeight A = 0 := by
  rw [boolMatrixWeight, card_eq_zero, filter_eq_empty_iff]
  rintro ⟨i, j⟩ - hij
  exact hA {i} {j} (card_singleton i) (card_singleton j) fun i' hi' j' hj' => by
    rw [mem_singleton.mp hi', mem_singleton.mp hj']
    exact hij

/-- Monotonicity in the rectangle threshold: a `k`-free matrix is `k'`-free for all `k ≤ k'`. -/
theorem IsRectangleFreeMatrix.mono {A : Matrix α β Bool} {k k' : ℕ}
    (hA : IsRectangleFreeMatrix A k) (hk : k ≤ k') : IsRectangleFreeMatrix A k' := by
  intro I J hI hJ hall
  obtain ⟨I', hI'sub, hI'card⟩ := exists_subset_card_eq (s := I) (hI ▸ hk)
  obtain ⟨J', hJ'sub, hJ'card⟩ := exists_subset_card_eq (s := J) (hJ ▸ hk)
  exact hA I' J' hI'card hJ'card fun i hi j hj => hall i (hI'sub hi) j (hJ'sub hj)

/-- Reindexing rows and columns preserves `k`-rectangle-freeness. -/
theorem isRectangleFreeMatrix_reindex (e₁ : α ≃ α') (e₂ : β ≃ β') (A : Matrix α β Bool) (k : ℕ) :
    IsRectangleFreeMatrix (Matrix.reindex e₁ e₂ A) k ↔ IsRectangleFreeMatrix A k := by
  classical
  refine ⟨fun h I J hI hJ hall => ?_, fun h I J hI hJ hall => ?_⟩
  · refine h (I.map e₁.toEmbedding) (J.map e₂.toEmbedding) (by rw [card_map, hI])
      (by rw [card_map, hJ]) fun i' hi' j' hj' => ?_
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hi'
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hj'
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.coe_toEmbedding,
      Equiv.symm_apply_apply] using hall i hi j hj
  · refine h (I.map e₁.symm.toEmbedding) (J.map e₂.symm.toEmbedding) (by rw [card_map, hI])
      (by rw [card_map, hJ]) fun i hi j hj => ?_
    obtain ⟨i', hi', hieq⟩ := mem_map.mp hi
    obtain ⟨j', hj', hjeq⟩ := mem_map.mp hj
    rw [← hieq, ← hjeq]
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.coe_toEmbedding]
      using hall i' hi' j' hj'

/-- The number of `2`-element subsets of a finite type `α` is `C(|α|, 2)`. -/
theorem card_twoSubsets [Fintype α] :
    Fintype.card {s : Finset α // #s = 2} = (Fintype.card α).choose 2 := by
  rw [Fintype.card_subtype, ← card_univ, ← card_powersetCard]
  congr 1
  ext s
  simp only [mem_filter, mem_univ, mem_powersetCard, subset_univ, true_and]

/-- Sergeev's *`2`-rectangle lift* of `A : Matrix α β Bool`, indexed by `2`-element subsets of `α`
and `β`, with entry `(r, c)` equal to `true` iff `r × c` is an all-`true` `2 × 2` submatrix of `A`
([Sergeev2014ORComplement], p. 2). -/
@[expose] def twoRectMatrix (A : Matrix α β Bool) :
    Matrix {r : Finset α // #r = 2} {c : Finset β // #c = 2} Bool :=
  Matrix.of fun r c => @decide (∀ (i) (_ : i ∈ r.1) (j) (_ : j ∈ c.1), A i j = true)
    (Finset.decidableDforallFinset (_hp := fun _ _ => Finset.decidableDforallFinset))

/-- Entry characterization of `twoRectMatrix`. -/
@[simp] theorem twoRectMatrix_apply (A : Matrix α β Bool)
    (r : {r : Finset α // #r = 2}) (c : {c : Finset β // #c = 2}) :
    twoRectMatrix A r c = true ↔ ∀ i ∈ r.1, ∀ j ∈ c.1, A i j = true := by
  simp only [twoRectMatrix, Matrix.of_apply, decide_eq_true_eq]

private theorem two_mul_choose_two_add (d : ℕ) : 2 * d.choose 2 + d = d ^ 2 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    linarith [ih, show (d + 1) ^ 2 = d ^ 2 + 2 * d + 1 by ring]

private theorem card_twoSubsets_subset [Fintype α] [DecidableEq α] (S : Finset α) :
    #(univ.filter fun r : {r : Finset α // #r = 2} => r.1 ⊆ S) = (#S).choose 2 := by
  rw [← card_powersetCard 2 S]
  refine card_bij (fun r _ => r.1) (fun r hr => mem_powersetCard.mpr ⟨(mem_filter.mp hr).2, r.2⟩)
    (fun _ _ _ _ => Subtype.ext) fun s hs => ?_
  rw [mem_powersetCard] at hs
  exact ⟨⟨s, hs.2⟩, mem_filter.mpr ⟨mem_univ _, hs.1⟩, rfl⟩

/-- Core Cauchy–Schwarz step counting `2 × 2` rectangles via `σ = ∑ i, C(a_i, 2)`. -/
private theorem rowPairSum_mul_sub_le_two_mul_choose_mul_boolMatrixWeight_twoRectMatrix
    [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    let σ := ∑ i : α, (#(univ.filter fun j : β => A i j = true)).choose 2
    let n := (Fintype.card β).choose 2
    σ * (σ - n) ≤ 2 * n * boolMatrixWeight (twoRectMatrix A) := by
  classical
  intro σ n
  set colCov : {c : Finset β // #c = 2} → Finset α :=
    fun c => univ.filter fun i : α => ∀ j ∈ c.1, A i j = true with hcolCov
  -- Double count `(i, c)` with `c.1 ⊆ {j | A i j = true}`.
  have hsum_b : ∑ c : {c : Finset β // #c = 2}, #(colCov c) = σ := by
    simp only [hcolCov, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← card_twoSubsets_subset, card_filter]
    refine sum_congr rfl fun c _ => ?_
    congr 1
    simp only [subset_iff, mem_filter, mem_univ, true_and]
  -- Count `2`-rectangles column-pair by column-pair: `|B| = ∑ c, C(#(colCov c), 2)`.
  have hsum_B : ∑ c : {c : Finset β // #c = 2}, (#(colCov c)).choose 2 =
      boolMatrixWeight (twoRectMatrix A) := by
    rw [boolMatrixWeight]
    have hsplit : #(univ.filter fun p : {r : Finset α // #r = 2} × {c : Finset β // #c = 2} =>
        twoRectMatrix A p.1 p.2 = true) =
        ∑ c : {c : Finset β // #c = 2},
          #(univ.filter fun r : {r : Finset α // #r = 2} => r.1 ⊆ colCov c) := by
      rw [← card_sigma]
      refine card_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => (p.2, p.1)) ?_ ?_ (fun _ _ => rfl)
        (fun _ _ => rfl) <;> intro p hp <;> simpa only [mem_coe, mem_filter, mem_univ, true_and,
          twoRectMatrix_apply, mem_sigma, hcolCov, subset_iff] using hp
    rw [hsplit]
    exact sum_congr rfl fun c _ => (card_twoSubsets_subset (colCov c)).symm
  -- Apply Cauchy–Schwarz over the `n = C(|β|, 2)` column pairs.
  have hsq_b : 2 * boolMatrixWeight (twoRectMatrix A) + σ =
      ∑ c : {c : Finset β // #c = 2}, #(colCov c) ^ 2 := by
    rw [← hsum_B, ← hsum_b, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun c _ => two_mul_choose_two_add _
  have hcs : σ ^ 2 ≤ n * (2 * boolMatrixWeight (twoRectMatrix A) + σ) := by
    have := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun c : {c : Finset β // #c = 2} =>
      #(colCov c))
    rwa [card_univ, card_twoSubsets, hsum_b, ← hsq_b] at this
  rw [Nat.mul_sub_left_distrib, tsub_le_iff_right]
  linarith only [hcs]

/-- If every row of `A : Matrix α β Bool` has at least `d` entries equal to `true`, then
`(|α| * C(d, 2)) * (|α| * C(d, 2) - C(|β|, 2)) ≤
  2 * C(|β|, 2) * boolMatrixWeight (twoRectMatrix A)`. -/
theorem mul_sub_le_two_mul_choose_mul_boolMatrixWeight_twoRectMatrix [Fintype α] [Fintype β]
    (A : Matrix α β Bool) {d : ℕ}
    (hd : ∀ i : α, d ≤ #(univ.filter fun j : β => A i j = true)) :
    (Fintype.card α * d.choose 2) * (Fintype.card α * d.choose 2 - (Fintype.card β).choose 2) ≤
      2 * (Fintype.card β).choose 2 * boolMatrixWeight (twoRectMatrix A) := by
  have hle : Fintype.card α * d.choose 2 ≤
      ∑ i : α, (#(univ.filter fun j : β => A i j = true)).choose 2 := by
    calc Fintype.card α * d.choose 2
        = ∑ _i : α, d.choose 2 := by rw [sum_const, card_univ, smul_eq_mul]
      _ ≤ ∑ i : α, (#(univ.filter fun j : β => A i j = true)).choose 2 :=
          sum_le_sum fun i _ => Nat.choose_le_choose 2 (hd i)
  exact (Nat.mul_le_mul hle (Nat.sub_le_sub_right hle _)).trans
    (rowPairSum_mul_sub_le_two_mul_choose_mul_boolMatrixWeight_twoRectMatrix A)

/-- **Sergeev's Lemma 1** ([Sergeev2014ORComplement], p. 2): every `m × m` Boolean matrix `A`
(`m = |α|`) with weight `|A| ≥ 2 m^{3/2}` (stated in exact integer form as `4 * m ^ 3 ≤ |A| ^ 2`)
satisfies `|A| ^ 4 ≤ 32 * m ^ 4 * boolMatrixWeight (twoRectMatrix A)`. -/
theorem pow_four_boolMatrixWeight_le_mul_boolMatrixWeight_twoRectMatrix [Fintype α]
    (A : Matrix α α Bool) (hA : 4 * Fintype.card α ^ 3 ≤ boolMatrixWeight A ^ 2) :
    boolMatrixWeight A ^ 4 ≤ 32 * Fintype.card α ^ 4 * boolMatrixWeight (twoRectMatrix A) := by
  set m := Fintype.card α with hm_def
  set W := boolMatrixWeight A with hW_def
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · have hW0 : W = 0 := by simpa [← hm_def, hm0] using boolMatrixWeight_le_card_mul A
    simp [hW0]
  -- First Cauchy–Schwarz step over the `m` rows: `W ^ 2 ≤ 4 * m * σ`.
  let rowWt : α → ℕ := fun i => #(univ.filter fun j : α => A i j = true)
  set σ := ∑ i : α, (rowWt i).choose 2
  have hsq_a : 2 * σ + W = ∑ i : α, rowWt i ^ 2 := by
    rw [hW_def, boolMatrixWeight_eq_sum_row A, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => two_mul_choose_two_add _
  have hcs_a : W ^ 2 ≤ m * (2 * σ + W) := by
    have := sq_sum_le_card_mul_sum_sq (s := univ) (f := rowWt)
    rwa [card_univ, ← hm_def, ← boolMatrixWeight_eq_sum_row A, ← hW_def, ← hsq_a] at this
  have h2m_le_W : 2 * m ≤ W := by
    refine (Nat.pow_le_pow_iff_left two_ne_zero).mp ?_
    linarith only [hA, Nat.pow_le_pow_right hm_pos (show 2 ≤ 3 by norm_num)]
  have hW_sigma : W ^ 2 ≤ 4 * m * σ := by
    linarith only [hcs_a, Nat.mul_le_mul_right W h2m_le_W]
  -- Deduce `2 * C(m, 2) ≤ m ^ 2 ≤ σ`.
  have hm2_le_sigma : m ^ 2 ≤ σ := by
    refine Nat.le_of_mul_le_mul_left (?_ : 4 * m * m ^ 2 ≤ 4 * m * σ) (by positivity)
    linarith only [hA, hW_sigma]
  set n := m.choose 2
  have h2n_le_m2 : 2 * n ≤ m ^ 2 := by
    have := two_mul_choose_two_add m
    omega
  have hsigma2 : σ ^ 2 ≤ 2 * m ^ 2 * boolMatrixWeight (twoRectMatrix A) := by
    have hsub : σ ≤ 2 * (σ - n) := by omega
    calc σ ^ 2 ≤ 2 * (σ * (σ - n)) := by linarith only [Nat.mul_le_mul_left σ hsub]
      _ ≤ 2 * (2 * n * boolMatrixWeight (twoRectMatrix A)) := Nat.mul_le_mul_left 2
          (rowPairSum_mul_sub_le_two_mul_choose_mul_boolMatrixWeight_twoRectMatrix A)
      _ ≤ 2 * m ^ 2 * boolMatrixWeight (twoRectMatrix A) := by rw [← mul_assoc]; gcongr
  linarith only [Nat.pow_le_pow_left hW_sigma 2, Nat.mul_le_mul_left (16 * m ^ 2) hsigma2]

private theorem le_card_biUnion_of_card_twoSubsets [DecidableEq α]
    {R : Finset {r : Finset α // #r = 2}} {k : ℕ} (hk : 1 ≤ k)
    (hR : #R = (k - 1).choose 2 + 1) :
    k ≤ #(R.biUnion Subtype.val) := by
  by_contra hlt
  have hle : #(R.biUnion Subtype.val) ≤ k - 1 := by omega
  have hinj : #R ≤ #((R.biUnion Subtype.val).powersetCard 2) := by
    rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩]
    refine card_le_card fun s hs => ?_
    obtain ⟨r, hr, rfl⟩ := mem_map.mp hs
    exact mem_powersetCard.mpr ⟨subset_biUnion_of_mem Subtype.val hr, r.2⟩
  rw [card_powersetCard] at hinj
  have hch := hinj.trans (Nat.choose_le_choose 2 hle)
  omega

/-- **Sergeev's Lemma 2** ([Sergeev2014ORComplement], p. 2): if `A : Matrix α β Bool` is `k`-free,
then its `2`-rectangle lift `twoRectMatrix A` is `(C(k - 1, 2) + 1)`-free. -/
theorem IsRectangleFreeMatrix.twoRectMatrix {A : Matrix α β Bool} {k : ℕ}
    (hA : IsRectangleFreeMatrix A k) :
    IsRectangleFreeMatrix (Cslib.twoRectMatrix A) ((k - 1).choose 2 + 1) := by
  classical
  have hk : 1 ≤ k := hA.pos
  intro R C hR hC hall
  have hUR : k ≤ #(R.biUnion Subtype.val) := le_card_biUnion_of_card_twoSubsets hk hR
  have hUC : k ≤ #(C.biUnion Subtype.val) := le_card_biUnion_of_card_twoSubsets hk hC
  obtain ⟨I, hIsub, hIcard⟩ := exists_subset_card_eq hUR
  obtain ⟨J, hJsub, hJcard⟩ := exists_subset_card_eq hUC
  refine hA I J hIcard hJcard fun i hi j hj => ?_
  obtain ⟨r, hrR, hir⟩ := mem_biUnion.mp (hIsub hi)
  obtain ⟨c, hcC, hjc⟩ := mem_biUnion.mp (hJsub hj)
  have hrc := hall r hrR c hcC
  rw [twoRectMatrix_apply] at hrc
  exact hrc i hir j hjc

end Cslib
