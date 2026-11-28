/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, new `Mathlib/LinearAlgebra/Matrix/Permanent/Grenet.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BranchingProgramDeterminant
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset

/-!
# Grenet's determinantal representation of the permanent

The permanent of an `n × n` matrix `A` over a commutative ring is the determinant of a
`(2ⁿ - 1) × (2ⁿ - 1)` matrix `grenetMatrix A` whose entries are entries of `A`, `0` or `-1`
[Grenet][Grenet2011].

Grenet's construction starts from an algebraic branching program on the subsets of
`{0, …, n - 1}`, with source `∅` and sink the whole set. For `j ∉ S`, an arc goes from `S` to
`insert j S` with weight `A #S j`, an entry of row `#S`. A path from `∅` to the whole set adds
the columns one at a time, row by row, so it reads off a permutation `σ` with weight
`∏ k, A k (σ k)`. The value of the program is the permanent. The colex order on the subsets
numbers the vertices in topological order, because a proper subset comes earlier in colex. The
step from the branching program to the determinant is
`Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul`. That step deletes the row of the
sink and the column of the source from `N - 1`, where `N` is the weighted adjacency matrix.
Grenet instead merges the source and the sink, puts loops of weight `1` on the other vertices,
and fixes the sign for even `n` by giving weight `-1` to the loops of the first layer. Here every
vertex other than the merged source and sink carries `-1` on the diagonal, and the adjugate
formula absorbs the sign, so no parity case split is needed. This is Grenet's construction with
a different sign normalization.

Grenet states the result over fields of characteristic other than two; in characteristic two
the permanent is the determinant. The identity `Matrix.permanent_eq_det_grenetMatrix` holds over
every commutative ring.

## Main definitions

* `Matrix.grenetMatrix`: Grenet's `(2ⁿ - 1) × (2ⁿ - 1)` matrix of an `n × n` matrix.

## Main results

* `Matrix.permanent_eq_det_grenetMatrix`: `A.permanent = A.grenetMatrix.det`.
* `Matrix.grenetMatrix_apply_eq`: every entry of `A.grenetMatrix` is an entry of `A`, `0` or
  `-1`.

## References

* [B. Grenet, *An upper bound for the permanent versus determinant problem*][Grenet2011],
  Lemma and Theorem.
-/

public section

open Finset

namespace Matrix.Grenet

variable {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α]

/-- The weight of the arcs from `S` to `T` in Grenet's branching program with layer weights
`w`: an arc from `S` to `insert j S`, for `j ∉ S`, has weight `w #S j`. -/
private def arc (w : ℕ → α → R) (S T : Finset α) : R :=
  ∑ j ∈ Sᶜ, if insert j S = T then w #S j else 0

/-- The total weight of the paths of length `k` from `∅` to `T`. Such a path adds the elements
`f 0, …, f (k - 1)` of `T` in order, with weight `∏ i, w i (f i)`. -/
private def pathSum (w : ℕ → α → R) (k : ℕ) (T : Finset α) : R :=
  ∑ f : Fin k → α with Function.Injective f ∧ univ.image f = T, ∏ i : Fin k, w i (f i)

omit [Fintype α] in
/-- The image of `Fin.snoc g j` is the image of `g` with `j` added. -/
private theorem image_snoc {k : ℕ} (g : Fin k → α) (j : α) :
    univ.image (Fin.snoc g j : Fin (k + 1) → α) = insert j (univ.image g) :=
  coe_injective (by simp [Set.image_univ, Fin.range_snoc])

omit [Fintype α] in
/-- `Fin.snoc g j` enumerates `T` exactly when `j ∈ T` and `g` enumerates `T.erase j`. -/
private theorem snoc_injective_and_image_eq_iff {k : ℕ} (g : Fin k → α) (j : α)
    (T : Finset α) :
    (Function.Injective (Fin.snoc g j : Fin (k + 1) → α) ∧
        univ.image (Fin.snoc g j : Fin (k + 1) → α) = T) ↔
      j ∈ T ∧ Function.Injective g ∧ univ.image g = T.erase j := by
  rw [Fin.snoc_injective_iff, image_snoc]
  refine ⟨?_, fun ⟨hjT, hg, hT⟩ => ⟨⟨hg, ?_⟩, by rw [hT, insert_erase hjT]⟩⟩
  · rintro ⟨⟨hg, hj⟩, rfl⟩
    exact ⟨mem_insert_self _ _, hg, (erase_insert (by simpa using hj)).symm⟩
  · rintro ⟨i, rfl⟩
    exact (mem_erase.mp (hT ▸ mem_image_of_mem _ (mem_univ i))).1 rfl

/-- A path of length `k + 1` into `T` is a path of length `k` into `T.erase j` followed by an
arc adding `j`. -/
private theorem pathSum_succ (w : ℕ → α → R) (k : ℕ) (T : Finset α) :
    pathSum w (k + 1) T = ∑ j ∈ T, pathSum w k (T.erase j) * w k j := by
  unfold pathSum
  rw [sum_filter, ← (Fin.snocEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.snocEquiv_apply, snoc_injective_and_image_eq_iff, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rw [← sum_filter_add_sum_filter_not univ (· ∈ T),
    sum_eq_zero (s := univ.filter (· ∉ T)) fun j hj => sum_eq_zero fun _ _ =>
      by simp [(mem_filter.mp hj).2],
    add_zero, filter_mem_eq_inter, univ_inter]
  exact sum_congr rfl fun j hj => by simp [sum_filter, sum_mul, hj]

/-- The only path of length `0` is the empty path into `∅`. -/
private theorem pathSum_zero (w : ℕ → α → R) (T : Finset α) :
    pathSum w 0 T = if T = ∅ then 1 else 0 := by
  unfold pathSum
  rw [sum_filter, Fintype.sum_unique]
  by_cases hT : T = ∅ <;> simp [hT, Function.injective_of_subsingleton, eq_comm]

/-- The path sums `q T = pathSum w #T T` satisfy `q = Pi.single ∅ 1 + q ᵥ* arc w`. -/
private theorem pathSum_card_eq (w : ℕ → α → R) (T : Finset α) :
    pathSum w #T T = (Pi.single (∅ : Finset α) (1 : R) : Finset α → R) T +
      ∑ S : Finset α, pathSum w #S S * arc w S T := by
  have hsum : ∑ S : Finset α, pathSum w #S S * arc w S T =
      ∑ j ∈ T, pathSum w #(T.erase j) (T.erase j) * w #(T.erase j) j := by
    simp only [arc, mul_sum]
    rw [sum_comm' (t' := univ) (s' := fun j => univ.filter (j ∉ ·)) (fun _ _ => by simp),
      ← sum_filter_add_sum_filter_not univ (· ∈ T),
      sum_eq_zero (s := univ.filter (· ∉ T)) fun y hy => sum_eq_zero fun x _ => by
        rw [ite_eq_right fun h : insert y x = T => (mem_filter.mp hy).2 (h ▸ mem_insert_self y x),
          mul_zero],
      add_zero, filter_mem_eq_inter, univ_inter]
    refine sum_congr rfl fun y hy => ?_
    rw [sum_eq_single_of_mem (T.erase y) (by simp)]
    · rw [ite_eq_left (insert_erase hy)]
    · intro x hx hne
      rw [ite_eq_right fun h => hne (by rw [← h, erase_insert (mem_filter.mp hx).2]), mul_zero]
  rw [hsum]
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp [pathSum_zero]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (card_ne_zero.2 hT)
    rw [hk, pathSum_succ, Pi.single_eq_of_ne hT.ne_empty, zero_add]
    exact sum_congr rfl fun j hj => by rw [card_erase_of_mem hj, hk, Nat.succ_sub_one]

/-- Arcs only go from a set to a strictly larger set. -/
private theorem arc_eq_zero_of_not_ssubset (w : ℕ → α → R) {S T : Finset α} (h : ¬S ⊂ T) :
    arc w S T = 0 :=
  sum_eq_zero fun _ hj =>
    ite_eq_right fun hST : insert _ S = T => h (hST ▸ ssubset_insert (mem_compl.1 hj))

/-- The layer weights of the permanent: row `k` of `A`, or `0` past the last row. -/
private def weight {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (k : ℕ) (j : Fin n) : R :=
  if hk : k < n then A ⟨k, hk⟩ j else 0

/-- The paths from `∅` to the whole set are the permutations, so their total weight is the
permanent. -/
private theorem pathSum_univ_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    pathSum (weight A) n univ = A.permanent := by
  rw [← permanent_transpose]
  unfold pathSum permanent
  have hmem (f : Fin n → Fin n) : f ∈ univ.filter
      (fun f => Function.Injective f ∧ univ.image f = univ) ↔ Function.Bijective f := by
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => Finite.injective_iff_bijective.mp h.1,
      fun h => ⟨h.1, image_univ_of_surjective h.2⟩⟩
  rw [sum_subtype _ hmem (fun f => ∏ i : Fin n, weight A i (f i))]
  refine Fintype.sum_equiv Equiv.bijectiveEquiv _ _ fun f => ?_
  simp only [weight, Fin.isLt, dite_true, transpose_apply]
  rfl

/-- The colex order on `Finset (Fin n)` is finite. -/
private local instance instFintypeColex (n : ℕ) : Fintype (Colex (Finset (Fin n))) :=
  Fintype.ofEquiv _ toColex

/-- There are `2ⁿ` subsets of `Fin n`, written `2ⁿ - 1 + 1` to delete one row and column. -/
private theorem card_colex (n : ℕ) : Fintype.card (Colex (Finset (Fin n))) = 2 ^ n - 1 + 1 := by
  rw [Fintype.card_congr toColex.symm, Fintype.card_finset, Fintype.card_fin,
    Nat.sub_add_cancel Nat.one_le_two_pow]

/-- The subsets of `Fin n`, numbered in colex order. -/
private noncomputable def colexEquiv (n : ℕ) : Fin (2 ^ n - 1 + 1) ≃ Finset (Fin n) :=
  (Fintype.orderIsoFinOfCardEq (Colex (Finset (Fin n))) (card_colex n)).toEquiv.trans
    toColex.symm

/-- Unfolding `colexEquiv`. -/
private theorem colexEquiv_apply (n : ℕ) (i : Fin (2 ^ n - 1 + 1)) :
    colexEquiv n i = ofColex (Fintype.orderIsoFinOfCardEq _ (card_colex n) i) :=
  rfl

/-- The first subset in colex order is `∅`. -/
private theorem colexEquiv_zero (n : ℕ) : colexEquiv n 0 = ∅ := by
  rw [colexEquiv_apply, ← bot_eq_zero, OrderIso.map_bot]
  rfl

/-- The last subset in colex order is the whole set. -/
private theorem colexEquiv_last (n : ℕ) : colexEquiv n (Fin.last _) = univ := by
  rw [colexEquiv_apply, ← Fin.top_eq_last, OrderIso.map_top]
  rfl

/-- A proper subset comes earlier in colex order. -/
private theorem lt_of_colexEquiv_ssubset {n : ℕ} {i j : Fin (2 ^ n - 1 + 1)}
    (h : colexEquiv n i ⊂ colexEquiv n j) : i < j := by
  have := Finset.Colex.toColex_lt_toColex_of_ssubset h
  rw [colexEquiv_apply, colexEquiv_apply, toColex_ofColex, toColex_ofColex] at this
  exact (OrderIso.lt_iff_lt _).1 this

end Matrix.Grenet

namespace Matrix

open Grenet

variable {R : Type*} [CommRing R]

/-- **Grenet's matrix** of an `n × n` matrix `A` [Grenet][Grenet2011]. Number the subsets of
`{0, …, n - 1}` in colex order, from `∅` to the whole set. Rows are indexed by all subsets but
the whole set, columns by all subsets but `∅`. The entry at `(S, T)` is `A #S j` if
`T = insert j S` with `j ∉ S`, `-1` if `S = T`, and `0` otherwise. Its determinant is the
permanent of `A` (`Matrix.permanent_eq_det_grenetMatrix`). -/
noncomputable def grenetMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (2 ^ n - 1)) (Fin (2 ^ n - 1)) R :=
  ((Matrix.of fun i j => arc (weight A) (colexEquiv n i) (colexEquiv n j)) - 1).submatrix
    Fin.castSucc Fin.succ

/-- **Grenet's theorem** [Grenet][Grenet2011]: the permanent of an `n × n` matrix over a
commutative ring is the determinant of a `(2ⁿ - 1) × (2ⁿ - 1)` matrix whose entries are entries
of `A`, `0` or `-1` (`Matrix.grenetMatrix_apply_eq`). Grenet states it over fields of
characteristic other than two; the identity holds over every commutative ring. -/
theorem permanent_eq_det_grenetMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    A.permanent = A.grenetMatrix.det := by
  set N : Matrix (Fin (2 ^ n - 1 + 1)) (Fin (2 ^ n - 1 + 1)) R :=
    Matrix.of fun i j => arc (weight A) (colexEquiv n i) (colexEquiv n j)
  set q : Fin (2 ^ n - 1 + 1) → R := fun i =>
    pathSum (weight A) #(colexEquiv n i) (colexEquiv n i)
  have hN : ∀ i j, j ≤ i → N i j = 0 := fun i j hji =>
    arc_eq_zero_of_not_ssubset _ fun h => (lt_of_colexEquiv_ssubset h).not_ge hji
  have hq : q = Pi.single 0 1 + q ᵥ* N := funext fun i => by
    simp only [q, N, Pi.add_apply, vecMul, dotProduct, of_apply]
    rw [pathSum_card_eq, ← (colexEquiv n).sum_comp]
    simp only [← colexEquiv_zero n, Pi.single_apply, (colexEquiv n).injective.eq_iff]
  have hdet := eq_det_submatrix_sub_one_of_eq_single_add_vecMul N hN hq
  simp only [q, colexEquiv_last, card_univ, Fintype.card_fin, pathSum_univ_fin] at hdet
  exact hdet

/-- Every entry of Grenet's matrix is an entry of `A`, `0` or `-1`. -/
theorem grenetMatrix_apply_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (a b : Fin (2 ^ n - 1)) :
    (∃ i j, A.grenetMatrix a b = A i j) ∨ A.grenetMatrix a b = 0 ∨
      A.grenetMatrix a b = -1 := by
  have happ : A.grenetMatrix a b =
      arc (weight A) (colexEquiv n a.castSucc) (colexEquiv n b.succ) -
        (1 : Matrix _ _ R) a.castSucc b.succ := rfl
  by_cases hab : a.castSucc = b.succ
  · exact Or.inr (Or.inr (by
      rw [happ, hab, one_apply_eq, arc_eq_zero_of_not_ssubset _ (ssubset_irrefl _), zero_sub]))
  rw [happ, one_apply_ne hab, sub_zero, arc]
  set S := colexEquiv n a.castSucc
  set T := colexEquiv n b.succ
  by_cases hj : ∃ j ∉ S, insert j S = T
  · obtain ⟨j, hjS, hjT⟩ := hj
    rw [sum_eq_single_of_mem j (mem_compl.2 hjS) fun j' hj' hne =>
        ite_eq_right fun hj'T : insert j' S = T =>
          hne ((mem_insert.mp (hjT ▸ hj'T ▸ mem_insert_self j' S)).resolve_right (mem_compl.1 hj')),
      ite_eq_left hjT, weight]
    split_ifs with hk
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl
      (sum_eq_zero fun j hj' => ite_eq_right fun h => hj ⟨j, mem_compl.1 hj', h⟩))

end Matrix
